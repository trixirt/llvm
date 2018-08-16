//===-- CodeSizeOutliner.cpp - Propagate constants through calls -----===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This pass implements a simple algorithm for outlining congruent chains of
//  instructions from the current module.
//
//===----------------------------------------------------------------------===//
#include "llvm/Transforms/IPO/CodeSizeOutliner.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/IntervalMap.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/SmallBitVector.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/SparseBitVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/BranchProbabilityInfo.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/OptimizationRemarkEmitter.h"
#include "llvm/Analysis/ProfileSummaryInfo.h"
#include "llvm/Analysis/RegionInfo.h"
#include "llvm/Analysis/TargetTransformInfo.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DiagnosticInfo.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Pass.h"
#include "llvm/Transforms/IPO.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/Outliner.h"
#include <sstream>

using namespace llvm;

static cl::opt<unsigned> MinOccurrences(
    "cso-min-occurrences", cl::init(2), cl::Hidden,
    cl::desc(
        "Min number of occurrences to consider a candidate for outlining."));
static cl::opt<unsigned> MinInstructionLength(
    "cso-min-instructions", cl::init(1), cl::Hidden,
    cl::desc(
        "Min number of instructions to consider a candidate for outlining."));
static cl::opt<unsigned>
    MinBenefit("cso-min-benefit", cl::init(1), cl::Hidden,
               cl::desc("Min estimated benefit to be considered profitable."));

#define DEBUG_TYPE "codesizeoutliner"
STATISTIC(NumOccurrencesOutlined, "Number of occurrences outlined");
STATISTIC(NumCandidatesOutlined, "Number of outlined functions created");

namespace {
/// \brief A struct representing an input into an outlined function.
struct Input {
  Input(unsigned short InstrNo, unsigned short OpNo)
      : InstrNo(InstrNo), OpNo(OpNo) {}
  Input() {}
  /// The index of the instruction in the sequence.
  unsigned short InstrNo;
  /// The index of the operand into the instruction.
  unsigned short OpNo;
};

/// \brief Contains the information necessary for condensing constant inputs.
// Condense any constant int inputs to the outlined function.
// example:
//  void outlinedFn(int a, int b);
// call 1: outlinedFn(1, 2);
// call 2: outlinedFn(3, 4);
// We identify that in all occurrences that arg 2 is simply
//  a difference of 1 from arg 1.
// void outlinedFn(int a) {
//   int b = a + 1;
//   ...
// }
struct ConstantCondenseInstance {
  /// The base input.
  Input BaseInput;

  /// The difference from the base input.
  std::vector<APInt> Diffs;

  /// The input/op numbers for the condensed arguments.
  std::vector<Input> InputSeqs;

  /// The cost of this instance.
  unsigned Cost;

  ConstantCondenseInstance(Input BaseInput, unsigned Reserve)
      : BaseInput(BaseInput) {
    Diffs.reserve(Reserve);
    InputSeqs.reserve(Reserve);
  }
};

/// \brief Information necessary for outlining specific to IR outlining.
struct AdditionalCandidateData {
  /// Inputs into this candidate : Vector<Instr Index, Op#>.
  std::vector<Input> InputSeq;

  /// Outputs from this candidate.
  SparseBitVector<> Outputs;

  /// The constant condense instances.
  std::vector<ConstantCondenseInstance> ConstInsts;

  /// The number of registers used in a call to the candidate.
  unsigned NumCallRegisters = 0;
};

/// \brief Holds information about a particular instruction.
struct InstructionInfo {
  /// The inputs/operands going into this instruction.
  SmallVector<unsigned, 4> InputIndexes;

  /// The index of the farthest use of this instruction in the same block
  /// parent.
  unsigned FarthestInSameBlockOutput = 0;

  /// The size cost of this instruction.
  unsigned Cost = -1;
};
} // namespace

namespace {

// Helper function for getting the size in bits of a type
//  in a multiple of /p WidestRegister.
unsigned getTypeSize(const DataLayout &DL, Type *Ty, unsigned WidestRegister) {
  if (Ty->isTokenTy())
    return 0u;
  if (Ty->isPointerTy())
    return WidestRegister;
  unsigned TypeSize = DL.getTypeSizeInBits(Ty->getScalarType());
  unsigned RegisterRemainder = TypeSize % WidestRegister;
  if (RegisterRemainder > 0)
    TypeSize += WidestRegister - RegisterRemainder;
  return TypeSize;
}

// Helper function for getting the register usage of type /p Ty.
unsigned getRegisterUsage(const DataLayout &DL, Type *Ty,
                          unsigned WidestRegister) {
  unsigned ret = 0;
  // getTypeSize calls getTypeSizeInBits which expects that
  // the type size is non zero.  So check..
  if (Ty != nullptr && Ty->isSized())
    ret = getTypeSize(DL, Ty, WidestRegister) / WidestRegister;
  return ret;
}

// Helper to get the cost of a constant.
unsigned getGlobalValueCost(const Constant *C) {
  if (isa<Function>(C))
    return TargetTransformInfo::TCC_Free;
  if (isa<GlobalValue>(C))
    return TargetTransformInfo::TCC_Basic;
  const ConstantExpr *CE = dyn_cast<ConstantExpr>(C);
  if (!CE)
    return TargetTransformInfo::TCC_Free;
  if (CE->getOpcode() == Instruction::GetElementPtr) {
    unsigned Cost = TargetTransformInfo::TCC_Basic;
    Cost += getGlobalValueCost(CE->getOperand(0));
    for (unsigned i = 1, e = CE->getNumOperands(); i < e; ++i) {
      const Constant *COp = CE->getOperand(i);
      if (const ConstantInt *CI = dyn_cast<ConstantInt>(COp)) {
        if (!CI->isZero())
          ++Cost;
      } else
        ++Cost;
    }
    return Cost;
  }
  if (CE->isCast())
    return getGlobalValueCost(CE->getOperand(0));
  return TargetTransformInfo::TCC_Free;
}

/// \brief Helper struct containing mapping information for a module.
class IROutlinerMapper : public OutlinerMapper {
public:
  ///
  ///  Instruction Information Utilities.
  ///

  // Get the instruction at index /p Idx.
  Instruction *getInstr(unsigned Idx) {
    return OutlinerMapper::getInstr<Instruction>(Idx);
  }
  // Get the operand /p OpIdx of the instruction at index /p Idx.
  Value *getInstrOp(unsigned Idx, unsigned OpIdx) {
    return getInstr(Idx)->getOperand(OpIdx);
  }
  // Get the parent function of the instruction at /p Idx.
  Function *getInstrFunction(size_t Idx) {
    return getInstr(Idx)->getFunction();
  }
  // Get or compute the cost of the instruction at /p InstrIdx.
  unsigned getInstrCost(TargetTransformInfo &TTI, size_t InstrIdx) {
    InstructionInfo *Info = InstrInfo[InstrIdx];
    if (Info->Cost == unsigned(-1)) {
      Info->Cost = computeInstrCost(TTI, InstrIdx);
#ifndef NDEBUG
      Instruction *I = getInstr(InstrIdx);
      LLVM_DEBUG(dbgs() << "Instruction Cost : " << Info->Cost << " : " << *I
                        << "\n");
#endif
    }
    return Info->Cost;
  }
  // Get the instruction info attached to index /p InstrIdx
  InstructionInfo &getInstrInfo(size_t InstrIdx) {
    InstructionInfo *Info = InstrInfo[InstrIdx];
    assert(Info && "Queried instruction has no info created.");
    return *Info;
  }
  // Create instruction info for the instruction at /p InstrIdx
  void createInstrInfo(size_t InstrIdx) {
    InstructionInfo *&Info = InstrInfo[InstrIdx];
    assert(!Info && "Instruction info already generated.");
    Info = new (InfoAllocator.Allocate()) InstructionInfo();
    Instruction *Inst = getInstr(InstrIdx);
    BasicBlock *InstPar = Inst->getParent();

    /// Inputs.
    unsigned NumOperands = Inst->getNumOperands();
    Info->InputIndexes.reserve(NumOperands);
    for (unsigned InIt = 0; InIt < NumOperands; ++InIt) {
      unsigned IIdx = 0;
      Value *Op = Inst->getOperand(InIt);
      Instruction *IOp = dyn_cast<Instruction>(Op);
      if (IOp && IOp->getParent() == InstPar) {
        unsigned FoundIIdx = getInstrIdx(IOp);
        if (FoundIIdx <= InstrIdx)
          IIdx = FoundIIdx;
      } else if (isa<BasicBlock>(Op))
        break;
      Info->InputIndexes.emplace_back(IIdx);
    }

    /// Outputs.
    for (User *Usr : Inst->users()) {
      Instruction *I = dyn_cast<Instruction>(Usr);
      if (!I || I->getParent() != InstPar) {
        Info->FarthestInSameBlockOutput = -1;
        break;
      }
      unsigned IIdx = getInstrIdx(I);
      if (IIdx > Info->FarthestInSameBlockOutput)
        Info->FarthestInSameBlockOutput = IIdx;
    }
  }

  ///
  ///  Candidate Information Utilities.
  ///

  // Get the data attached to the provided candidate.
  AdditionalCandidateData &getCandidateData(const OutlineCandidate &OC) {
    return *OutlineCandData[OC.ID];
  }
  // Create candidate data.
  void createCandidateData(size_t Count) {
    size_t NewSize = OutlineCandData.size() + Count;
    OutlineCandData.reserve(NewSize);
    for (size_t i = 0; i < Count; ++i)
      OutlineCandData.emplace_back(new (DataAlloc.Allocate())
                                       AdditionalCandidateData());
  }

  void initAdditionalData() {
    InstrInfo.assign(getNumMappedInstructions(), nullptr);
  }

private:
  // Compute the cost of an instruction.
  unsigned computeInstrCost(TargetTransformInfo &TTI, unsigned InstrIdx) {
    Instruction *I = getInstr(InstrIdx);
    const DataLayout &Layout = I->getModule()->getDataLayout();
    bool HasFreeAddressComp = TTI.getAddressComputationCost(I->getType()) == 0;
    unsigned Cost = 0;

    // Estimate the cost of each instruction.
    switch (I->getOpcode()) {
    case Instruction::Add:
      if (any_of(I->operand_values(),
                 [](Value *V) { return isa<ConstantInt>(V); }))
        Cost = TargetTransformInfo::TCC_Free;
      else
        Cost = TargetTransformInfo::TCC_Basic;
      break;
    case Instruction::FDiv:
      Cost = TargetTransformInfo::TCC_Basic;
      break;
    case Instruction::FRem:
    case Instruction::SDiv:
    case Instruction::SRem:
    case Instruction::UDiv:
    case Instruction::URem:
      Cost = TargetTransformInfo::TCC_Basic * 2;
      break;
    case Instruction::Store: {
      StoreInst *SI = cast<StoreInst>(I);
      Type *SITy = SI->getValueOperand()->getType();
      Cost = getRegisterUsage(Layout, SITy, TTI.getRegisterBitWidth(false));
      break;
    }
    case Instruction::Load: {
      LoadInst *LI = cast<LoadInst>(I);
      Type *LITy = LI->getType();
      Cost = getRegisterUsage(Layout, LITy, TTI.getRegisterBitWidth(false));

      // Be conservative about the cost of loads given they may be folded.
      //  Estimating a lower cost helps to prevent over estimating the
      //  benefit of this instruction.
      Value *Ptr = LI->getPointerOperand();
      auto WillLoadFold = [&]() -> bool {
        // We likely can't fold from a phi node.
        if (isa<PHINode>(Ptr))
          return false;
        // Floating point values will likely need to be materialized.
        if (LITy->isFloatingPointTy() && !isa<GetElementPtrInst>(Ptr))
          return false;
        // If the address comp is free then any globals won't affect the cost.
        if (HasFreeAddressComp)
          return true;
        // Non Free address comp will likely need to load globals or values
        //  used more than once.
        return !isa<Constant>(Ptr) && I->hasOneUse();
      };
      if (WillLoadFold())
        --Cost;
      break;
    }
    case Instruction::Invoke:
    case Instruction::Call:
      Cost = computeCallCost(I, TTI);
      break;
    case Instruction::GetElementPtr: {
      GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(I);
      Cost = TTI.getUserCost(GEP);

      // Be conservative about non free global geps that appear more than once
      //  in a function, the gep is likely to be materialized only once.
      GlobalVariable *GVar = dyn_cast<GlobalVariable>(GEP->getPointerOperand());
      if (!GVar)
        break;
      if (HasFreeAddressComp) {
        for (User *Usr : GVar->users()) {
          Instruction *InstrUsr = dyn_cast<Instruction>(Usr);
          if (!InstrUsr || InstrUsr == I)
            continue;
          if (InstrUsr->getFunction() != I->getFunction())
            continue;
          Cost = TargetTransformInfo::TCC_Free;
          break;
        }
        break;
      }
      break;
    }
    default:
      Cost = TTI.getUserCost(I);
      break;
    }

    // Accumulate additional cost from constant and global operands.
    for (auto OpI = I->op_begin(), OpE = I->op_end(); OpI != OpE; ++OpI) {
      Constant *COp = dyn_cast<Constant>(&*OpI);
      if (!COp)
        continue;

      // Get the code size cost of any constant int immediates.
      if (ConstantInt *CI = dyn_cast<ConstantInt>(COp)) {
        if (isa<CallInst>(I))
          continue;
        Cost += TTI.getIntImmCodeSizeCost(I->getOpcode(), OpI->getOperandNo(),
                                          CI->getValue(), CI->getType());
      }
      // If we don't have free address computation any use of globals
      //  can actually result in more cost.
      else if (!HasFreeAddressComp)
        Cost += getGlobalValueCost(COp);
    }
    return Cost;
  }

  // Helper for getting the cost of a call instruction.
  unsigned computeCallCost(Instruction *I, TargetTransformInfo &TTI) {
    CallSite CS(I);
    Function *F = CS.getCalledFunction();

    // For intrinsics and non lowered calls, use the default cost.
    if (F && F->isDeclaration()) {
      if (F->isIntrinsic())
        return TTI.getUserCost(I);
      if (!TTI.isLoweredToCall(F))
        return TargetTransformInfo::TCC_Basic;
    }
    // Otherwise compute the register usage of the call instead of just
    // a param count.
    const DataLayout &Layout = CS.getParent()->getModule()->getDataLayout();
    unsigned WidestRegister = TTI.getRegisterBitWidth(false);
    // Collect the total size of the parameters.
    unsigned TotalParamSizeInBits = 0;
    for (Value *Op : CS.args()) {
      TotalParamSizeInBits +=
          getTypeSize(Layout, Op->getType(), WidestRegister);
    }
    // Potential reload for call return.
    if (!I->use_empty()) {
      Type *RetTy = CS.getType();
      TotalParamSizeInBits += getTypeSize(Layout, RetTy, WidestRegister);
    }
    // Call instruction.
    unsigned CallCost = TargetTransformInfo::TCC_Basic;
    // Setting up the function pointer to be called.
    if (!F)
      CallCost += TargetTransformInfo::TCC_Basic;
    // Parameter/output register usage.
    CallCost += TotalParamSizeInBits / WidestRegister;
    return CallCost;
  }

  /// Stores information for parallel instruction in InstrVec.
  std::vector<InstructionInfo *> InstrInfo;
  SpecificBumpPtrAllocator<InstructionInfo> InfoAllocator;

  /// Stores extra candidate data.
  std::vector<AdditionalCandidateData *> OutlineCandData;
  SpecificBumpPtrAllocator<AdditionalCandidateData> DataAlloc;
};

/// \brief A specific instance of an outlined candidate.
struct FunctionSplicer {
  FunctionSplicer(bool EmitProfileData)
      : EmitProfileData(EmitProfileData), NumOutlined(0) {
    // Prepare the function attributes that we don't want to inherit from any
    // parents.
    NonInheritAttrs.addAttribute(Attribute::AlwaysInline);
    NonInheritAttrs.addAttribute(Attribute::ArgMemOnly);
    NonInheritAttrs.addAttribute(Attribute::InaccessibleMemOnly);
    NonInheritAttrs.addAttribute(Attribute::InaccessibleMemOrArgMemOnly);
    NonInheritAttrs.addAttribute(Attribute::InlineHint);
    NonInheritAttrs.addAttribute(Attribute::Naked);
    NonInheritAttrs.addAttribute(Attribute::NoInline);
    NonInheritAttrs.addAttribute(Attribute::NoRecurse);
    NonInheritAttrs.addAttribute(Attribute::ReturnsTwice);
    NonInheritAttrs.addAttribute(Attribute::ReadOnly);
    NonInheritAttrs.addAttribute(Attribute::ReadNone);
    NonInheritAttrs.addAttribute(Attribute::NoReturn);
    NonInheritAttrs.addAttribute(Attribute::WriteOnly);
  }

  // Reset the outliner to prepare for a new instance.
  void prepareForNewCandidate(const OutlineCandidate &OC,
                              IROutlinerMapper &OM) {
    OutlinedFn = nullptr;
    InitialStartIdx = *OC.begin();
    AdditionalCandidateData &Data = OM.getCandidateData(OC);

    // Handle output type.
    LLVMContext &Ctx = OM.getInstr(InitialStartIdx)->getContext();
    unsigned NumOutputs = Data.Outputs.count();
    if (NumOutputs == 0)
      OutputType = Type::getVoidTy(Ctx);
    else if (NumOutputs == 1) {
      Instruction *OnlyOut =
          OM.getInstr(InitialStartIdx + Data.Outputs.find_first());
      OutputType = OnlyOut->getType();
    } else {
      // Collect information about the outputs of this new candidate.
      SmallVector<Type *, 8> OutputTypes;
      for (size_t OutputIdx : Data.Outputs) {
        Type *OutTy = OM.getInstr(InitialStartIdx + OutputIdx)->getType();
        OutputTypes.push_back(OutTy);
      }

      // Build a struct type to hold the outputs.
      OutputType = StructType::get(Ctx, OutputTypes);
    }
  }

  // Outline a new occurrence of an outline chain.
  void outlineOccurrence(const OutlineCandidate &OC, unsigned StartIdx,
                         IROutlinerMapper &OM) {
    ++NumOccurrencesOutlined;
    Instruction *Tail = OM.getInstr(StartIdx + (OC.Len - 1));
    Function *ParentFn = Tail->getFunction();
    bool InitialOccur = !OutlinedFn;
    AdditionalCandidateData &Data = OM.getCandidateData(OC);

    /// Split the outline chain into its own block.
    Instruction *Head = OM.getInstr(StartIdx);
    BasicBlock *EntryBlock = Head->getParent();
    // Split our chain instance into a separate block for extraction.
    /// Split up to the head if we aren't at the front of our block.
    if (Head != &EntryBlock->front() ||
        EntryBlock == &ParentFn->getEntryBlock())
      EntryBlock = EntryBlock->splitBasicBlock(Head->getIterator());
    /// Split after the tail.
    BasicBlock *Exit = nullptr;
    if (!isa<TerminatorInst>(Tail)) {
      auto SentinalIt = Tail->getNextNode()->getIterator();
      Exit = EntryBlock->splitBasicBlock(SentinalIt);
    }

    // Create a new block to patch the outlined section.
    BasicBlock *OutlineBlock =
        BasicBlock::Create(ParentFn->getContext(), "cso.patch", ParentFn);

    // Create parameter vec for the new call.
    unsigned NumOutputs = Data.Outputs.count();
    std::vector<Value *> Args;
    Args.reserve(Data.InputSeq.size());

    // Build inputs/outputs in order.
    for (Input &I : Data.InputSeq)
      Args.push_back(OM.getInstrOp(StartIdx + I.InstrNo, I.OpNo));

    // Replace branches to entry block.
    EntryBlock->replaceAllUsesWith(OutlineBlock);

    // Get the first valid debug info.
    DebugLoc CallLoc;
    if (ParentFn->getSubprogram())
      for (auto It = Head->getIterator(), E = EntryBlock->end();
           !CallLoc && It != E; ++It)
        CallLoc = It->getDebugLoc();

    // If this is not the first occurrence we merge metadata and attributes for
    //  the outlined instructions.
    if (!InitialOccur) {
      unsigned KnownIDs[] = {LLVMContext::MD_tbaa,
                             LLVMContext::MD_alias_scope,
                             LLVMContext::MD_noalias,
                             LLVMContext::MD_range,
                             LLVMContext::MD_invariant_load,
                             LLVMContext::MD_nonnull,
                             LLVMContext::MD_invariant_group,
                             LLVMContext::MD_align,
                             LLVMContext::MD_dereferenceable,
                             LLVMContext::MD_fpmath,
                             LLVMContext::MD_dereferenceable_or_null};

      // Merge special state.
      for (unsigned InitI = InitialStartIdx, CurI = StartIdx,
                    InitE = InitialStartIdx + OC.Len;
           InitI < InitE; ++InitI, ++CurI) {
        Instruction *InitII = OM.getInstr(InitI);
        Instruction *CurII = OM.getInstr(CurI);
        // Make sure the alignment is valid as we skip it during congruency
        // finding.
        if (LoadInst *LI = dyn_cast<LoadInst>(InitII))
          LI->setAlignment(std::min(LI->getAlignment(),
                                    cast<LoadInst>(CurII)->getAlignment()));
        else if (StoreInst *SI = dyn_cast<StoreInst>(InitII))
          SI->setAlignment(std::min(SI->getAlignment(),
                                    cast<StoreInst>(CurII)->getAlignment()));
        // Make sure that no tails are propagated properly.
        else if (CallInst *CI = dyn_cast<CallInst>(InitII)) {
          auto TCK = cast<CallInst>(CurII)->getTailCallKind();
          if (TCK != CallInst::TCK_Tail)
            CI->setTailCallKind(TCK);
        }
        // Be conservative about flags like nsw/nuw.
        else
          InitII->andIRFlags(OM.getInstr(CurI));

        // Merge metadata.
        DebugLoc DL = InitII->getDebugLoc();
        if (DL && DL != CurII->getDebugLoc())
          InitII->setDebugLoc(DebugLoc());
        combineMetadata(InitII, CurII, KnownIDs);
      }

      // Merge function attribute data.
      AttributeFuncs::mergeAttributesForInlining(*OutlinedFn, *ParentFn);

      // Make sure that all of the parameters are the correct type.
      FunctionType *FTy = OutlinedFn->getFunctionType();
      for (unsigned i = 0, e = Args.size(); i < e; ++i) {
        Value *&Arg = Args[i];
        Type *ParamTy = FTy->getParamType(i);
        if (ParamTy != Arg->getType())
          Arg = CastInst::Create(CastInst::BitCast, Arg, ParamTy, "",
                                 OutlineBlock);
      }

      // Otherwise we outline the initial occurrence.
    } else
      outlineInitialOccurrence(OC, OM, StartIdx, Args, EntryBlock);

    // Create the patchup for the outline section.
    Instruction *PatchupI;
    if (InvokeInst *II = dyn_cast<InvokeInst>(Tail)) {
      // If we have an invoke then we create a reload block for the values.
      InvokeInst *NewII =
          InvokeInst::Create(OutlinedFn, II->getNormalDest(),
                             II->getUnwindDest(), Args, "", OutlineBlock);
      NewII->setCallingConv(OutlinedFn->getCallingConv());
      NewII->setDebugLoc(CallLoc);
      PatchupI = NewII;
      // Otherwise create a call instruction.
    } else {
      CallInst *CI = CallInst::Create(OutlinedFn, Args, "", OutlineBlock);
      CI->setCallingConv(OutlinedFn->getCallingConv());
      CI->setDebugLoc(CallLoc);
      PatchupI = CI;
    }

    // Replace uses of outputs and create reloads.
    if (NumOutputs == 1) {
      Instruction *OnlyOut = OM.getInstr(StartIdx + Data.Outputs.find_first());
      OnlyOut->replaceUsesOutsideBlock(PatchupI, EntryBlock);
    } else if (NumOutputs != 0) {
      unsigned OutputNum = 0;
      for (size_t OutputIdx : Data.Outputs) {
        Instruction *Out = OM.getInstr(StartIdx + OutputIdx);
        Value *Reload =
            ExtractValueInst::Create(PatchupI, OutputNum++, "", OutlineBlock);
        Out->replaceUsesOutsideBlock(Reload, EntryBlock);
      }
    }

    // An invoke occurrence already has a valid terminator.
    if (!isa<InvokeInst>(Tail))
      BranchInst::Create(Exit, OutlineBlock);

    // Delete the dead entry block.
    if (!InitialOccur)
      EntryBlock->eraseFromParent();
  }

  // \brief Finalize this function as an outline instance.
  void finalize(const OutlineCandidate &OC, IROutlinerMapper &OM) {
    // Check to see if our tail is an invoke instruction. If so then we
    // transform it into a call.
    Instruction *Tail = OM.getInstr(InitialStartIdx + OC.Len - 1);
    if (InvokeInst *II = dyn_cast<InvokeInst>(Tail)) {
      SmallVector<Value *, 8> IIArgs(II->arg_operands());
      SmallVector<OperandBundleDef, 2> Bundles;
      II->getOperandBundlesAsDefs(Bundles);
      CallInst *CI =
          CallInst::Create(II->getCalledValue(), IIArgs, Bundles, "", II);
      CI->setAttributes(II->getAttributes());
      CI->setCallingConv(II->getCallingConv());
      CI->setDebugLoc(II->getDebugLoc());
      CI->copyMetadata(*II);
      II->replaceAllUsesWith(CI);
      II->eraseFromParent();
    }

    // Re-unique the inputs to the function.
    uniqueInputs(OM.getCandidateData(OC));

    // Set the final function name.
    OutlinedFn->setName(Twine("cso_") + Twine(NumOutlined++));

    // Debug.
    LLVM_DEBUG(dbgs() << "** Outlining : " << OutlinedFn->getName() << "\n"
                      << " Candidate : " << OC.ID << "\n"
                      << " occurrences : " << OC.size() << "\n"
                      << " size : " << OC.Len << "\n"
                      << " benefit : " << OC.Benefit << "\n"
                      << " benefit per occurrence : " << OC.BenefitPerOccur
                      << "\n");
  }

private:
  // Re-Unique the inputs for the outlined function.
  //  example:
  //   void outlinedFn(int, int);
  // call 1: outlinedFn(a, a);
  // call 2: outlinedFn(b, b);
  // We identify that parameters 1 and 2 are the same
  //  for each callsite, so we condense them.
  void uniqueInputs(AdditionalCandidateData &Data) {
    FunctionType *CurFnTy = OutlinedFn->getFunctionType();
    unsigned NumInputs = CurFnTy->getNumParams();

    // Map <ArgNo> to <Congruency Group Idx>
    DenseMap<unsigned, unsigned> ArgNoToCG, RhsArgNoToCG;
    std::vector<BitVector> ArgCongruencyGroups, RhsArgCGroups;

    // Helper function to collect the information on the use of inputs in the
    // outlined function. This identifies which arguments are actually congruent
    // to each other for a specific function call.
    auto CollectInputInfo = [&](CallSite &CS,
                                DenseMap<unsigned, unsigned> &ANoToCG,
                                std::vector<BitVector> &ArgCGroups) {
      ArgCGroups.reserve(NumInputs);
      for (unsigned i = 0, e = NumInputs; i < e; ++i) {
        // We already evaluated the equivalencies for this arg.
        if (ANoToCG.count(i))
          continue;
        Value *Op = CS.getArgOperand(i);
        BitVector CurrentGroup(NumInputs);
        CurrentGroup.set(i);
        ANoToCG.try_emplace(i, ArgCGroups.size());
        for (unsigned j = i + 1; j < e; ++j) {
          if (ANoToCG.count(j))
            continue;
          if (CS.getArgOperand(j) == Op) {
            CurrentGroup.set(j);
            ANoToCG.try_emplace(j, ArgCGroups.size());
          }
        }
        ArgCGroups.emplace_back(std::move(CurrentGroup));
      }
    };

    // Build initial equivalences from the first call.
    auto UserIt = OutlinedFn->user_begin();
    CallSite FirstCS(cast<Instruction>(*UserIt));
    ++UserIt;
    CollectInputInfo(FirstCS, ArgNoToCG, ArgCongruencyGroups);

    // If we have the same amount of congruency groups as we do arguments,
    //   the they are already unique.
    if (NumInputs == ArgCongruencyGroups.size())
      return;
    // Check every other user to see if the equivalencies hold up.
    BitVector ResolvedInputs(NumInputs);
    // BitVector helper to hold non congruent matches between argument groups.
    BitVector NonCongruentLeft;
    for (auto UserE = OutlinedFn->user_end(); UserIt != UserE; ++UserIt) {
      CallSite CS(cast<Instruction>(*UserIt));
      RhsArgCGroups.clear();
      RhsArgNoToCG.clear();
      CollectInputInfo(CS, RhsArgNoToCG, RhsArgCGroups);
      ResolvedInputs.reset();
      for (unsigned i = 0, e = NumInputs; i < e; ++i) {
        if (ResolvedInputs.test(i))
          continue;
        BitVector &LhsGroup = ArgCongruencyGroups[ArgNoToCG[i]];
        BitVector &RhsGroup = RhsArgCGroups[RhsArgNoToCG[i]];

        /// Build non congruent arguments between the groups.
        NonCongruentLeft = LhsGroup;
        /// Congruent matches.
        LhsGroup &= RhsGroup;
        assert(LhsGroup.count() > 0);

        // Non congruent sets on both sides still act as a congruency group.
        NonCongruentLeft ^= LhsGroup;

        // Mark arguments as handled.
        for (unsigned SetBit : LhsGroup.set_bits())
          ResolvedInputs.set(SetBit);
        if (NonCongruentLeft.count() == 0)
          continue;

        // Move the non congruent matches from the left group to a
        //   new congruency group.
        unsigned NewGroupId = ArgCongruencyGroups.size();
        ArgCongruencyGroups.emplace_back(std::move(NonCongruentLeft));

        // Move non congruent matches to a new congruency group
        //   and remove them from the top level mapping.
        for (unsigned SetBit : ArgCongruencyGroups.back().set_bits())
          ArgNoToCG[SetBit] = NewGroupId;
      }
    }

    // No inputs can be condensed.
    if (NumInputs == ArgCongruencyGroups.size())
      return;

    // Build new function from the condensed inputs.
    std::vector<Type *> NewFnTys;
    for (auto &It : ArgCongruencyGroups)
      NewFnTys.push_back(CurFnTy->getParamType(It.find_first()));

    // Create the merged function.
    FunctionType *NewFnTy =
        FunctionType::get(CurFnTy->getReturnType(), NewFnTys, false);
    Function *MergedFn = Function::Create(NewFnTy, OutlinedFn->getLinkage(), "",
                                          OutlinedFn->getParent());
    MergedFn->takeName(OutlinedFn);
    MergedFn->copyAttributesFrom(OutlinedFn);

    /// Move Fn Body.
    MergedFn->getBasicBlockList().splice(MergedFn->begin(),
                                         OutlinedFn->getBasicBlockList());

    // Remap the arguments.
    for (Argument &Arg : OutlinedFn->args()) {
      Value *Repl = std::next(MergedFn->arg_begin(), ArgNoToCG[Arg.getArgNo()]);
      Arg.replaceAllUsesWith(Repl);
      Repl->takeName(&Arg);
    }

    // Rewrite the calls to this function with calls to the merged function.
    std::vector<Value *> CallArgs;
    for (auto U = OutlinedFn->use_begin(), E = OutlinedFn->use_end(); U != E;) {
      Instruction *OldI = cast<Instruction>(U->getUser());
      CallSite CS(OldI);
      ++U;
      CallArgs.clear();
      /// Map call args by their congruency group.
      for (auto &It : ArgCongruencyGroups)
        CallArgs.push_back(CS.getArgOperand(It.find_first()));
      /// Create the new call.
      Instruction *NewI;
      if (CallInst *CI = dyn_cast<CallInst>(OldI)) {
        CallInst *NewCall = CallInst::Create(MergedFn, CallArgs, "", CI);
        NewCall->setCallingConv(CI->getCallingConv());
        NewCall->setTailCall(CI->isTailCall());
        NewI = NewCall;
      } else if (InvokeInst *II = dyn_cast<InvokeInst>(OldI)) {
        InvokeInst *NewCall =
            InvokeInst::Create(MergedFn, II->getNormalDest(),
                               II->getUnwindDest(), CallArgs, "", II);
        NewCall->setCallingConv(II->getCallingConv());
        NewI = NewCall;
      } else
        llvm_unreachable("Invalid callsite for outlined function.");
      NewI->setDebugLoc(OldI->getDebugLoc());
      OldI->replaceAllUsesWith(NewI);
      OldI->eraseFromParent();
    }
    OutlinedFn->eraseFromParent();
    OutlinedFn = MergedFn;
  }

  // \brief Outline the initial occurrence of this chain.
  void outlineInitialOccurrence(const OutlineCandidate &OC,
                                IROutlinerMapper &OM, size_t StartIdx,
                                ArrayRef<Value *> Args, BasicBlock *Entry) {
    Function *ParentFn = Entry->getParent();

    /// Function type for outlined function.
    SmallVector<Type *, 8> Tys;
    Tys.reserve(Args.size());
    for (Value *Arg : Args)
      Tys.push_back(Arg->getType());
    FunctionType *FTy = FunctionType::get(OutputType, Tys, false);

    /// Create function and move outlined block.
    OutlinedFn = Function::Create(FTy, GlobalValue::PrivateLinkage, "",
                                  Entry->getModule());
    OutlinedFn->setCallingConv(CallingConv::Fast);
    OutlinedFn->setUnnamedAddr(GlobalValue::UnnamedAddr::Global);
    OutlinedFn->setAlignment(ParentFn->getAlignment());
    OutlinedFn->getBasicBlockList().splice(
        OutlinedFn->end(), Entry->getParent()->getBasicBlockList(),
        Entry->getIterator());

    /// Inherit attributes.
    LLVMContext &Ctx = OutlinedFn->getContext();
    AttributeSet AttrsToAdd =
        ParentFn->getAttributes().getAttributes(AttributeList::FunctionIndex);
    AttrsToAdd = AttrsToAdd.removeAttributes(Ctx, NonInheritAttrs);
    AttrsToAdd = AttrsToAdd.removeAttribute(Ctx, Attribute::AllocSize);
    OutlinedFn->addAttributes(AttributeList::FunctionIndex, AttrsToAdd);

    // Drop any uses of the outlined instructions as metadata.
    for (unsigned InitI = StartIdx, InitE = StartIdx + OC.Len; InitI < InitE;
         ++InitI) {
      Instruction *InitII = OM.getInstr(InitI);
      if (InitII->isUsedByMetadata())
        ValueAsMetadata::handleDeletion(InitII);
    }

    // FIXME: Ideally we should compute the real count for this function but
    //  for now we just tag it as cold.
    if (EmitProfileData)
      OutlinedFn->addFnAttr(Attribute::Cold);

    AdditionalCandidateData &Data = OM.getCandidateData(OC);

    // Erase the current terminator if we don't have an invoke.
    Instruction *CurTerm = Entry->getTerminator();
    if (!isa<InvokeInst>(CurTerm))
      CurTerm->eraseFromParent();

    /// Create stores for any output variables.
    Value *RetVal = nullptr;
    unsigned NumOutputs = Data.Outputs.count();
    if (NumOutputs == 1)
      RetVal = OM.getInstr(StartIdx + Data.Outputs.find_first());
    else if (NumOutputs != 0) {
      RetVal = UndefValue::get(OutputType);
      unsigned OutputNum = 0;
      for (size_t OutputIdx : Data.Outputs) {
        Instruction *Out = OM.getInstr(StartIdx + OutputIdx);
        InsertValueInst *Insert =
            InsertValueInst::Create(RetVal, Out, OutputNum++);
        Insert->insertAfter(Out);
        RetVal = Insert;
      }
    }
    ReturnInst::Create(Ctx, RetVal, Entry);

    /// Replace input operands with function arguments.
    auto ArgI = OutlinedFn->arg_begin();
    for (Input &I : Data.InputSeq) {
      Instruction *InputInst = OM.getInstr(StartIdx + I.InstrNo);
      InputInst->setOperand(I.OpNo, &*ArgI++);
    }

    /// Insert the constant param fixups.
    for (ConstantCondenseInstance &CInst : Data.ConstInsts) {
      Input &BaseInput = CInst.BaseInput;
      Value *CArg =
          OM.getInstrOp(InitialStartIdx + BaseInput.InstrNo, BaseInput.OpNo);
      Type *ConstantTy = CArg->getType();
      for (unsigned i = 0, e = CInst.Diffs.size(); i < e; ++i) {
        Input &I = CInst.InputSeqs[i];
        Instruction *ReplI = OM.getInstr(InitialStartIdx + I.InstrNo);
        APInt &Diff = CInst.Diffs[i];
        if (Diff.isNullValue()) {
          ReplI->setOperand(I.OpNo, CArg);
          continue;
        }
        Value *DiffVal = ConstantInt::get(ConstantTy, CInst.Diffs[i]);
        Value *Repl = BinaryOperator::CreateAdd(CArg, DiffVal, "", ReplI);
        ReplI->setOperand(I.OpNo, Repl);
      }
    }

    /// Cleanup for ignored instructions.
    for (auto It = Entry->begin(), E = Entry->end(); It != E;) {
      Instruction &I = *It;
      ++It;
      if (IntrinsicInst *II = dyn_cast<IntrinsicInst>(&I)) {
        switch (II->getIntrinsicID()) {
        default:
          continue;
        case Intrinsic::lifetime_start:
        case Intrinsic::lifetime_end:
        // FIXME: Fix this if we can have merged debug info.
        case Intrinsic::dbg_declare:
        case Intrinsic::dbg_value:
          break;
        }
        Entry->getInstList().erase(I.getIterator());
      }
    }
  }

  /// The function created after outlining.
  Function *OutlinedFn = nullptr;
  /// Function output type.
  Type *OutputType = nullptr;
  /// If we are emitting profile date during outlining.
  bool EmitProfileData;
  /// The index of the initial occurrence for the current splice.
  unsigned InitialStartIdx;
  /// Set of attributes that are not to be inherited from parent functions.
  AttrBuilder NonInheritAttrs;
  /// Number of functions that have been outlined.
  unsigned NumOutlined;
};

/// \brief Perform analysis and verification for the found outline candidates.
struct OutlinerAnalysis {
  OutlinerAnalysis(IROutlinerMapper &OM,
                   std::vector<OutlineCandidate> &CandidateList,
                   function_ref<TargetTransformInfo &(Function &)> GetTTI,
                   const DataLayout *Layout)
      : OM(OM), CandidateList(CandidateList), GetTTI(GetTTI), Layout(Layout) {}

  // Analyze our found candidates for benefit and correctness.
  void analyzeCandidateList() {
    // Generate instruction info for each instruction that is part
    //  of an occurrence.
    BitVector OccurInstrInfo(OM.getNumMappedInstructions());
    for (OutlineCandidate &OC : CandidateList)
      for (unsigned Occur : OC)
        OccurInstrInfo.set(Occur, Occur + OC.Len);
    for (unsigned Idx : OccurInstrInfo.set_bits())
      OM.createInstrInfo(Idx);

    // We verify the occurrences of each candidate are compatible.
    verifyOccurrenceCompatability();

    // Estimate the function type and benefit of each chain.
    computeFunctionType(0, CandidateList.size());

    // Analyze the currently profitable candidates for partitioning based
    //  upon equivalent inputs.
    analyzeInputsForPartitioning();

    // Estimate the benefit for each candidate.
    computeOutlineBenefit(0, CandidateList.size());

    // The last analysis is the register cost per occurrence.
    // This is very costly so we do this after selecting the profitable
    //  candidates.
    computeOutlineCallRegisterCost();
  }

private:
  // Helper cache for mapping which functions are compatible with each other.
  struct CompatibleAttrCache {
    unsigned getFnIdx(Function *F,
                      function_ref<TargetTransformInfo &(Function &)> GetTTI) {
      // Find an existing mapping of our function.
      auto It = FnToIdx.find(F);
      if (It != FnToIdx.end())
        return It->second;

      // Find a compatible function in the cache.
      for (auto &MapIt : FnToIdx) {
        if (!AttributeFuncs::areInlineCompatible(*F, *MapIt.first))
          continue;
        TargetTransformInfo &TTI = GetTTI(*MapIt.first);
        if (TTI.areInlineCompatible(F, MapIt.first)) {
          FnToIdx[F] = MapIt.second;
          return MapIt.second;
        }
      }

      // Insert our function.
      FnToIdx[F] = CacheIdx;
      return CacheIdx++;
    }

  private:
    DenseMap<Function *, unsigned> FnToIdx;
    unsigned CacheIdx = 0;
  };
  // Helper struct for verifying the compatibility of occurrences within a
  // candidate.
  struct VerifyInst {
    VerifyInst(CompatibleAttrCache *Cache) : Cache(Cache) {}
    VerifyInst() = default;
    void reset(Function *F) {
      Fn = F;
      Indices.clear();
    }
    bool compare(VerifyInst &R,
                 function_ref<TargetTransformInfo &(Function &)> GetTTI) {
      Function *LF = Fn, *RF = R.Fn;
      if (LF != RF)
        if (Cache->getFnIdx(LF, GetTTI) != Cache->getFnIdx(RF, GetTTI))
          return false;
      return Indices == R.Indices;
    }

    Function *Fn;
    std::vector<unsigned> Indices;
    CompatibleAttrCache *Cache;
  };

  // Verify the compatibilities of the occurrences in each candidate.
  void verifyOccurrenceCompatability() {
    // Vector of different verification leaders.
    std::vector<VerifyInst> VerificationCands;
    // Count of occurrences to an verification instance.
    std::vector<size_t> Counts;
    // Maps occurrences to the input index they belong to.
    std::vector<size_t> OccurrenceInputIdx;
    // Cache of attribute compatibility between functions.
    CompatibleAttrCache Cache;
    // Verification instance of the current occurrence being considered.
    VerifyInst CurrentOccurVerifyInst(&Cache);

    size_t CurrentCandidateListSize = CandidateList.size();
    for (size_t i = 0, e = CurrentCandidateListSize; i < e; ++i) {
      OutlineCandidate &OC = CandidateList[i];

      // Compute the input sequence for this occurrence.
      for (size_t Oi = OccurrenceInputIdx.size(), Oe = OC.size(); Oi < Oe;
           ++Oi) {
        unsigned Occur = OC.getOccurrence(Oi);
        CurrentOccurVerifyInst.reset(OM.getInstrFunction(Occur));
        for (size_t InstrIdx = Occur, InstrE = Occur + OC.Len;
             InstrIdx < InstrE; ++InstrIdx) {
          InstructionInfo &II = OM.getInstrInfo(InstrIdx);
          for (unsigned InIdx : II.InputIndexes) {
            // We only really need to verify inputs coming from within the
            // sequence. Other inputs simply help to verify the ordering.
            unsigned InputIdx = InIdx < Occur ? -1 : InIdx - Occur;
            CurrentOccurVerifyInst.Indices.push_back(InputIdx);
          }
        }

        // Check for existing mapping of this instance.
        auto It =
            std::find_if(VerificationCands.begin(), VerificationCands.end(),
                         [&](VerifyInst &L) {
                           return L.compare(CurrentOccurVerifyInst, GetTTI);
                         });
        if (It != VerificationCands.end()) {
          size_t InternalInputIt = It - VerificationCands.begin();
          ++Counts[InternalInputIt];
          OccurrenceInputIdx.push_back(InternalInputIt);
          continue;
        }
        unsigned OrigCapacity = CurrentOccurVerifyInst.Indices.capacity();
        OccurrenceInputIdx.push_back(VerificationCands.size());
        VerificationCands.emplace_back(std::move(CurrentOccurVerifyInst));
        CurrentOccurVerifyInst.Indices.reserve(OrigCapacity);
        Counts.push_back(1);
      }

      OutlineCandidate &Cur = CandidateList[i];
      size_t SharedSizeWithNext = Cur.SharedSizeWithNext;
      size_t IdxOfNext = i + 1;
      while (SharedSizeWithNext > 0 && !CandidateList[IdxOfNext].isValid())
        SharedSizeWithNext = CandidateList[IdxOfNext++].SharedSizeWithNext;
      size_t FirstOccur = Cur.getOccurrence(0);

      // Only split if needed.
      if (Counts.size() > 1)
        splitOutlineChain(i, Counts, OccurrenceInputIdx);

      // If we share a size with the next chain then we do cleanup and set up to
      //  reduce the amount of work we need to do during the next iteration.
      if (SharedSizeWithNext > 0 && CandidateList[IdxOfNext].isValid()) {
        // Get the cut off point for moving to the next candidate.
        size_t SharedCutOffPoint = 0;
        for (size_t InstrIdx = FirstOccur,
                    InstrE = FirstOccur + SharedSizeWithNext;
             InstrIdx < InstrE; ++InstrIdx) {
          InstructionInfo &II = OM.getInstrInfo(InstrIdx);
          SharedCutOffPoint += II.InputIndexes.size();
        }

        // Update the size of the internal inputs vectors.
        for (size_t InIt = 0, InE = VerificationCands.size(); InIt < InE;
             ++InIt)
          VerificationCands[InIt].Indices.resize(SharedCutOffPoint);

        // Don't bother merging if there is only one instance.
        if (Counts.size() == 1)
          continue;

        // Set resolved occurrences that point to the first vector.
        BitVector UnResolved(OccurrenceInputIdx.size(), true);
        for (size_t i = 0, e = OccurrenceInputIdx.size(); i < e; ++i)
          if (OccurrenceInputIdx[i] == 0)
            UnResolved.reset(i);
        // Condense the internal inputs vector in the case where two vectors are
        //  now equivalent given the smaller size.
        size_t InsertIdx = 1;
        for (size_t i = 1, e = VerificationCands.size(); i < e; ++i) {
          VerifyInst &VI = VerificationCands[i];
          auto RemapOccurIdxs = [&](size_t Old, size_t New) {
            for (size_t OccurIdx : UnResolved.set_bits()) {
              if (OccurrenceInputIdx[OccurIdx] == Old) {
                OccurrenceInputIdx[OccurIdx] = New;
                UnResolved.reset(OccurIdx);
              }
            }
          };
          // Try to remap to an existing instance.
          auto Remap = [&]() -> bool {
            for (size_t j = 0; j < InsertIdx; ++j) {
              if (VerificationCands[j].compare(VI, GetTTI)) {
                Counts[j] += Counts[i];
                RemapOccurIdxs(i, j);
                return true;
              }
            }
            return false;
          };

          // Update mapping with new instance.
          if (!Remap()) {
            if (i != InsertIdx) {
              Counts[InsertIdx] = Counts[i];
              RemapOccurIdxs(i, InsertIdx);
              VerificationCands[InsertIdx++] = std::move(VerificationCands[i]);
            } else
              ++InsertIdx;
          }
        }
        VerificationCands.resize(InsertIdx);
        Counts.resize(InsertIdx);
        continue;
      }
      // Otherwise we just cleanup what we used.
      VerificationCands.clear();
      Counts.clear();
      OccurrenceInputIdx.clear();
    }
  }

  // Split the OutlineChain at index /p CurrentChainIndex into N different
  // candidates with the provided memberships.
  void splitOutlineChain(size_t CurrentChainIndex,
                         const std::vector<size_t> &MembershipCounts,
                         const std::vector<size_t> &OccurrenceInputIdx) {
    OutlineCandidate *OrigChain = &CandidateList[CurrentChainIndex];
    SmallVector<size_t, 4> SplitChains(MembershipCounts.size(), -1);
    size_t FirstValid = 0;
    while (FirstValid < MembershipCounts.size() &&
           MembershipCounts[FirstValid] < MinOccurrences)
      ++FirstValid;
    if (FirstValid == MembershipCounts.size()) {
      OrigChain->invalidate();
      OrigChain->Occurrences.clear();
      OrigChain->SharedSizeWithNext = 0;
      return;
    }

    SplitChains[FirstValid] = CurrentChainIndex;

    // Add new chains for each valid count after the first.
    unsigned OrigLen = OrigChain->Len;
    for (size_t i = FirstValid + 1, e = MembershipCounts.size(); i < e; ++i) {
      size_t Count = MembershipCounts[i];
      if (Count < MinOccurrences)
        continue;
      SplitChains[i] = CandidateList.size();
      CandidateList.emplace_back(SplitChains[i], OrigLen);
      OutlineCandidate &NewChain = CandidateList.back();
      NewChain.Occurrences.reserve(Count);
    }

    // Move occurrences to their new parents.
    OrigChain = &CandidateList[CurrentChainIndex];
    for (size_t i = 0, e = OrigChain->size(); i < e; ++i) {
      size_t NewParentIdx = SplitChains[OccurrenceInputIdx[i]];
      if (NewParentIdx != CurrentChainIndex && NewParentIdx != size_t(-1)) {
        OutlineCandidate &NewParent = CandidateList[NewParentIdx];
        NewParent.Occurrences.push_back(OrigChain->Occurrences[i]);
      }
    }
    for (ssize_t i = OrigChain->size() - 1; i >= 0; --i)
      if (OccurrenceInputIdx[i] != FirstValid)
        OrigChain->removeOccurrence(i);

    // Update shared size information.
    if (CurrentChainIndex != 0) {
      OutlineCandidate &Prev = CandidateList[CurrentChainIndex - 1];
      if (Prev.SharedSizeWithNext > 0 &&
          Prev.getOccurrence(0) != OrigChain->getOccurrence(0))
        Prev.SharedSizeWithNext = 0;
    }
  }

  // Estimate the function type of each outline chain in the given range.
  void computeFunctionType(size_t StartIdx, size_t EndIdx) {
    std::vector<Value *> InputOperands;
    BitVector FoldableInputs;

    // Create candidate data for each of the candidates.
    OM.createCandidateData(EndIdx - StartIdx);
    for (size_t i = StartIdx; i < EndIdx; ++i) {
      OutlineCandidate &OC = CandidateList[i];
      if (OC.size() == 0)
        continue;
      AdditionalCandidateData &OCData = OM.getCandidateData(OC);
      unsigned FirstOccur = *OC.begin();

      // Compute the input sequence if needed.
      if (OCData.InputSeq.empty()) {
        // Inputs are operands that come from outside of the chain range.
        OCData.InputSeq.reserve(OC.Len);
        for (unsigned InstrIdx = FirstOccur, InstrE = FirstOccur + OC.Len;
             InstrIdx < InstrE; ++InstrIdx) {
          InstructionInfo &II = OM.getInstrInfo(InstrIdx);
          for (unsigned i = 0, e = II.InputIndexes.size(); i < e; ++i)
            if (II.InputIndexes[i] < FirstOccur)
              OCData.InputSeq.emplace_back(InstrIdx - FirstOccur, i);
        }
        computeCandidateOutputs(OC, OCData);

        // After computing we also compute the input sequences of chains
        //  that we share size with. We have already calculated the input
        //  sequence for this chain as it is a subset of our current
        //  sequence.
        OutlineCandidate *Cur = &OC;
        while (Cur->SharedSizeWithNext > 0) {
          OutlineCandidate *Next = std::next(Cur);
          AdditionalCandidateData &CurData = OM.getCandidateData(*Cur);
          AdditionalCandidateData &NextData = OM.getCandidateData(*Next);
          computeCandidateOutputs(*Next, NextData);
          for (unsigned i = 0, e = CurData.InputSeq.size(); i < e; ++i) {
            if (CurData.InputSeq[i].InstrNo >= Cur->SharedSizeWithNext) {
              NextData.InputSeq.assign(CurData.InputSeq.begin(),
                                       CurData.InputSeq.begin() + i);
              break;
            }
          }
          Cur = Next;
        }
      }

      // Verify the outputs.
      auto HasInvalidOutput = [&]() -> bool {
        // FIXME: Non invoke outputs may need special handling for dominance.
        unsigned NumOutputs = OCData.Outputs.count();
        if (isa<InvokeInst>(OM.getInstr(FirstOccur + OC.Len - 1))) {
          if (NumOutputs > 1)
            return true;
          if (NumOutputs == 1 && !OCData.Outputs.test(OC.Len - 1))
            return true;
        }
        return false;
      };
      if (HasInvalidOutput()) {
        OC.Occurrences.clear();
        OC.SharedSizeWithNext = 0;
        continue;
      }

      // Check to see if we share candidates with our predecessor. If we
      //   do then we can avoid rechecking candidates that we already have
      //   information for.
      size_t SharedOccurrencesWithPrev = 1;
      if (i > StartIdx) {
        OutlineCandidate &Prev = CandidateList[i - 1];
        if (Prev.SharedSizeWithNext > 0)
          SharedOccurrencesWithPrev = Prev.size();
      }

      // Try to constant fold inputs into the candidate.
      constantFoldInputs(FoldableInputs, OC, SharedOccurrencesWithPrev,
                         InputOperands);

      // Condense any remaining constant inputs if it is profitable.
      condenseConstantIntInputs(OC);
    }
  }

  // Remove any inputs into the candidate that will be constant folded.
  void constantFoldInputs(BitVector &FoldableInputs, OutlineCandidate &OC,
                          size_t SharedOccurrencesWithPrev,
                          std::vector<Value *> &InputOperands) {
    AdditionalCandidateData &OCData = OM.getCandidateData(OC);
    unsigned FirstOccur = *OC.begin();

    // Only recompute the input operands if we didn't share a size with the
    // previous chain.
    if (SharedOccurrencesWithPrev == 1) {
      // Get the operands for the first candidate.
      InputOperands.clear();
      FoldableInputs.set();
      FoldableInputs.resize(OCData.InputSeq.size(), true);
      for (size_t i = 0, e = OCData.InputSeq.size(); i < e; ++i) {
        Input &I = OCData.InputSeq[i];
        Value *Op = OM.getInstrOp(FirstOccur + I.InstrNo, I.OpNo);
        InputOperands.push_back(Op);
        if (!isa<Constant>(Op) && !isa<InlineAsm>(Op))
          FoldableInputs.reset(i);
      }
    } else {
      InputOperands.resize(OCData.InputSeq.size(), nullptr);
      FoldableInputs.resize(InputOperands.size());
    }

    // Check to see which inputs will be folded.
    auto OccurRange =
        make_range(OC.begin() + SharedOccurrencesWithPrev, OC.end());
    for (unsigned InputNo : FoldableInputs.set_bits()) {
      Input &I = OCData.InputSeq[InputNo];
      Value *IOp = InputOperands[InputNo];
      if (any_of(OccurRange, [&](unsigned Occur) {
            return OM.getInstrOp(Occur + I.InstrNo, I.OpNo) != IOp;
          }))
        FoldableInputs.reset(InputNo);
    }

    // Remove all of the inputs that will be folded.
    erase_if(OCData.InputSeq, [&](Input &I) -> bool {
      return FoldableInputs.test(&I - OCData.InputSeq.data());
    });
  }

  // Condense constant inputs that share a common operational difference
  //  between occurrences.
  void condenseConstantIntInputs(OutlineCandidate &OC) {
    AdditionalCandidateData &OCData = OM.getCandidateData(OC);
    if (!OCData.ConstInsts.empty())
      return;

    // Compute the set of inputs that are always constant.
    unsigned NumConstantIntInputs = OCData.InputSeq.size();
    if (NumConstantIntInputs < 2)
      return;
    BitVector ConstantInputs(NumConstantIntInputs, true);
    for (unsigned InputNo = 0, InputE = ConstantInputs.size(); InputNo < InputE;
         ++InputNo) {
      Input &I = OCData.InputSeq[InputNo];
      for (unsigned Occur : OC) {
        Value *InputOp = OM.getInstrOp(Occur + I.InstrNo, I.OpNo);
        if (!isa<ConstantInt>(InputOp)) {
          ConstantInputs.reset(InputNo);
          if (--NumConstantIntInputs == 1)
            return;
          break;
        }
      }
    }

    // Mapping between constant input number to function input number.
    std::vector<unsigned> ConstNumToFnInputMap;
    for (unsigned CInput : ConstantInputs.set_bits())
      ConstNumToFnInputMap.push_back(CInput);

    // Current instance variables.
    SmallVector<APInt, 8> InstDiff(ConstantInputs.count());
    BitVector InstMemberships(InstDiff.size());

    // The constant inputs that are condensed and need to be removed.
    BitVector RemovedInputs(ConstantInputs.size());

    // Iterate over the active constant parameters.
    auto InputI = ConstantInputs.set_bits_begin(),
         InputE = ConstantInputs.set_bits_end();
    for (unsigned ConstIntNum = 0; InputI != InputE; ++InputI, ++ConstIntNum) {
      // Don't recheck already handled inputs.
      if (RemovedInputs.test(*InputI))
        continue;

      InstMemberships.reset();
      InstDiff.clear();

      // Get the input sequence attached this param.
      Input &I = OCData.InputSeq[*InputI];

      // Run over each occurrence to compute the difference between the
      // operands.
      bool Success = true;
      for (unsigned i = 0, e = OC.size(); i < e; ++i) {
        bool InitialCollect = i == 0;
        unsigned Occur = OC.getOccurrence(i);

        // Get the base parameter we are working off of.
        Value *InputOp = OM.getInstrOp(Occur + I.InstrNo, I.OpNo);
        Type *OpTy = InputOp->getType();
        const APInt &FirstConstVal = cast<ConstantInt>(InputOp)->getValue();

        // Compute the difference for each input.
        auto NextInputI = InputI;
        ++NextInputI;
        for (unsigned NextCIntNum = 0; NextInputI != InputE;
             ++NextInputI, ++NextCIntNum) {

          // Already failed member.
          if (!InitialCollect &&
              !InstMemberships.test(NextCIntNum + ConstIntNum + 1))
            continue;

          // Already set to be removed.
          if (InitialCollect && RemovedInputs.test(*NextInputI)) {
            InstDiff.emplace_back(APInt());
            continue;
          }

          // Get the next constant operand.
          Input &NextI = OCData.InputSeq[*NextInputI];
          Value *NextOp = OM.getInstrOp(Occur + NextI.InstrNo, NextI.OpNo);
          ConstantInt *NextConstI = cast<ConstantInt>(NextOp);

          // Currently only consider constants of the same type.
          if (NextConstI->getType() != OpTy) {
            InstDiff.emplace_back(APInt());
            continue;
          }

          // Compute the difference.
          const APInt &NextConstVal = NextConstI->getValue();
          APInt Diff = NextConstVal - FirstConstVal;

          // Initial collection adds all diffs.
          if (InitialCollect) {
            InstDiff.emplace_back(Diff);
            InstMemberships.set(NextCIntNum + ConstIntNum + 1);
          } else if (InstDiff[NextCIntNum] != Diff)
            InstMemberships.reset(NextCIntNum + ConstIntNum + 1);
        }
        // No condensable constants.
        if (InstMemberships.none()) {
          Success = false;
          break;
        }
      }
      // No condensable constants.
      if (!Success)
        continue;

      // Create the new constant inst.
      Input &BaseInputSeq = OCData.InputSeq[ConstNumToFnInputMap[ConstIntNum]];
      OCData.ConstInsts.emplace_back(BaseInputSeq, InstMemberships.count());
      ConstantCondenseInstance &CInst = OCData.ConstInsts.back();

      // Add the input locations.
      SmallSet<SmallString<64>, 8> UniqueDiffs;
      unsigned ConstInputStart = ConstIntNum + 1;
      for (unsigned ConstInput : InstMemberships.set_bits()) {
        unsigned InputNo = ConstNumToFnInputMap[ConstInput];
        CInst.InputSeqs.push_back(OCData.InputSeq[InputNo]);
        APInt &Diff = InstDiff[ConstInput - ConstInputStart];
        CInst.Diffs.emplace_back(Diff);
        RemovedInputs.set(InputNo);

        // Add this diff.
        if (!Diff.isNullValue()) {
          SmallString<64> S;
          Diff.toStringSigned(S);
          UniqueDiffs.insert(S);
        }
      }

      // Add the amount of add instructions needed for this instance.
      CInst.Cost = UniqueDiffs.size();
    }

    // No condensable inputs.
    if (OCData.ConstInsts.empty())
      return;

    // Remove the dead inputs.
    for (unsigned i = 0, e = ConstantInputs.size(), InputNo = 0; i < e; ++i) {
      if (RemovedInputs.test(i))
        OCData.InputSeq.erase(OCData.InputSeq.begin() + InputNo);
      else
        ++InputNo;
    }
  }

  // Analyzes the input parameters to each candidate to see if we can get
  //  can get a more profitable chain by only considering some candidates.
  void analyzeInputsForPartitioning() {
    size_t CurrentListSize = CandidateList.size();
    SmallVector<BitVector, 8> NewCandidates;
    SmallDenseMap<Value *, unsigned> MembershipVals;
    std::vector<BitVector> Memberships;
    unsigned CurMembershipNum = 0;
    for (size_t i = 0; i < CurrentListSize; ++i) {
      OutlineCandidate &OC = CandidateList[i];
      AdditionalCandidateData &Data = OM.getCandidateData(OC);

      /// No inputs.
      if (OC.size() == 0 || Data.InputSeq.empty())
        continue;

      // Lambda helper for adding a member.
      auto AddMember = [&](Value *C, unsigned Occur) {
        auto It = MembershipVals.find(C);
        if (It == MembershipVals.end()) {
          if (CurMembershipNum == Memberships.size()) {
            BitVector New(OC.size());
            New.set(Occur);
            Memberships.emplace_back(std::move(New));
            MembershipVals.try_emplace(C, CurMembershipNum++);
            return;
          }
          MembershipVals.try_emplace(C, CurMembershipNum);
          BitVector &Cur = Memberships[CurMembershipNum++];
          Cur.reset();
          Cur.resize(OC.size());
          Cur.set(Occur);
          return;
        }
        BitVector &Cur = Memberships[It->second];
        Cur.set(Occur);
      };

      // Find the subsets of candidates that have the same constant input.
      NewCandidates.clear();
      for (size_t InputI = 0, InputE = Data.InputSeq.size(); InputI < InputE;
           ++InputI) {
        Input &In = Data.InputSeq[InputI];

        // Reset the memberships.
        CurMembershipNum = 0;
        MembershipVals.clear();

        // Add each constant input to a membership set.
        for (unsigned OccurI = 0, OccurE = OC.size(); OccurI < OccurE;
             ++OccurI) {
          unsigned Occur = OC.getOccurrence(OccurI);
          Value *IOp = OM.getInstrOp(Occur + In.InstrNo, In.OpNo);
          if (isa<Constant>(IOp))
            AddMember(IOp, OccurI);
        }

        // Add the memberships that will have a folded input.
        for (unsigned i = 0; i < CurMembershipNum; ++i) {
          BitVector &Members = Memberships[i];
          // Only one occurrence.
          if (Members.count() < 2)
            continue;
          // Already seen.
          auto It =
              std::find(NewCandidates.begin(), NewCandidates.end(), Members);
          if (It == NewCandidates.end())
            NewCandidates.emplace_back(Members);
        }
      }

      unsigned OrigLen = OC.Len;
      for (BitVector &NewCand : NewCandidates) {
        size_t NewChainIdx = CandidateList.size();
        CandidateList.emplace_back(NewChainIdx, OrigLen);
        OutlineCandidate &OGChain = CandidateList[i];
        OutlineCandidate &NewChain = CandidateList.back();
        NewChain.Occurrences.reserve(NewCand.count());
        for (unsigned OccurIdx : NewCand.set_bits())
          NewChain.Occurrences.push_back(OGChain.getOccurrence(OccurIdx));
      }
    }
    computeFunctionType(CurrentListSize, CandidateList.size());
  }

  // Compute the external outputs of a given candidate.
  void computeCandidateOutputs(OutlineCandidate &OC,
                               AdditionalCandidateData &Data) {
    // Outputs are internal instructions that have uses outside of the chain
    // range.
    Data.Outputs.clear();
    for (unsigned i = 0; i < OC.Len; ++i) {
      if (any_of(OC, [&](unsigned Occur) {
            InstructionInfo &II = OM.getInstrInfo(Occur + i);
            return II.FarthestInSameBlockOutput >= Occur + OC.Len;
          }))
        Data.Outputs.set(i);
    }
  }

  // Computes the estimated benefit of a set of potential functions.
  void computeOutlineBenefit(size_t StartIdx, size_t EndIdx) {
    SmallDenseSet<Value *, 8> UniqueInputOperands;
    SmallPtrSet<Constant *, 4> MaterializedValues;
    for (size_t i = StartIdx; i < EndIdx; ++i) {
      OutlineCandidate &OC = CandidateList[i];
      AdditionalCandidateData &Data = OM.getCandidateData(OC);

      /// Reset benefit metrics.
      OC.invalidate();

      // Sanity check.
      unsigned NumOccurences = OC.size();
      if (NumOccurences < MinOccurrences)
        continue;
      LLVM_DEBUG(dbgs() << "\nCandidate : " << OC.ID << "\n");
      LLVM_DEBUG(dbgs() << "Num : " << NumOccurences << "; Len : " << OC.Len
                        << "\n");

      /// Use the first occurrence as an example for cost analysis.
      unsigned FirstOccur = *OC.begin();
      /// Cost for each occurrence of the candidate.
      unsigned CostPerOccurence = 0;
      /// Cost for the outlined function.
      unsigned NewFunctionCost = 0;
      /// If this outline sequence contains a call.
      bool ContainsCall = false;

      /// New function contains a return.
      NewFunctionCost += 1;
      MaterializedValues.clear();

      // Estimate the cost of this chain of instructions.
      Function *FirstOccurFn = OM.getInstrFunction(FirstOccur);
      TargetTransformInfo &TTI = GetTTI(*FirstOccurFn);
      unsigned WidestRegister = TTI.getRegisterBitWidth(false);
      unsigned ChainCost = 0;
      for (size_t i = 0, e = OC.Len, InstIdx = FirstOccur; i < e;
           ++i, ++InstIdx) {
        ChainCost += OM.getInstrCost(TTI, InstIdx);
        Instruction *I = OM.getInstr(InstIdx);

        // Add in cost for constant materialization.
        for (Value *Op : I->operands()) {
          if (ConstantFP *CF = dyn_cast<ConstantFP>(Op)) {
            if (!MaterializedValues.insert(CF).second)
              continue;
            if (CF->isZero())
              continue;
            ++NewFunctionCost;
            if (CF->isNegative())
              ++NewFunctionCost;
          } else if (ConstantDataVector *CV =
                         dyn_cast<ConstantDataVector>(Op)) {
            if (CV->isZeroValue())
              continue;
            if (!CV->getType()->getScalarType()->isFloatingPointTy())
              continue;
            if (MaterializedValues.insert(CV).second)
              ++NewFunctionCost;
          }
        }

        switch (I->getOpcode()) {
        default:
          break;
        case Instruction::Invoke:
        case Instruction::Call: {
          ContainsCall = true;

          // If we tail then we don't need a return.
          if (i == e - 1)
            --NewFunctionCost;
          break;
        }
        case Instruction::Xor:
        case Instruction::Or: {
          auto &Info = OM.getInstrInfo(InstIdx);
          Instruction *L = dyn_cast<Instruction>(I->getOperand(0));
          Instruction *R = dyn_cast<Instruction>(I->getOperand(1));
          if (!L || !R)
            break;
          size_t TotalVal = 0;
          if (L->getOpcode() == Instruction::LShr) {
            if (R->getOpcode() != Instruction::Shl)
              break;
          } else if (L->getOpcode() == Instruction::Shl) {
            if (R->getOpcode() != Instruction::LShr)
              break;
          } else
            break;

          // Helper to get a constant value if it exists.
          auto AccumulateConstantIntVal = [&](Value *V) -> bool {
            ConstantInt *CI = dyn_cast<ConstantInt>(V);
            if (CI)
              TotalVal += CI->getZExtValue();
            return CI;
          };

          if (!AccumulateConstantIntVal(L->getOperand(0)) &&
              !AccumulateConstantIntVal(L->getOperand(1)))
            break;
          if (!AccumulateConstantIntVal(R->getOperand(0)) &&
              !AccumulateConstantIntVal(R->getOperand(1)))
            break;
          Type *Ty = I->getType();
          if (Layout->getTypeSizeInBits(Ty) == TotalVal) {
            unsigned FoldedCost = TargetTransformInfo::TCC_Basic * 2;
            // If they are inputs then we add cost for removing this
            //  folding oppurtunity.
            if (Info.InputIndexes[0] < FirstOccur ||
                Info.InputIndexes[1] < FirstOccur) {
              CostPerOccurence += FoldedCost;
            }
            // If they are then we remove the folded cost.
            else
              ChainCost -= FoldedCost;
          }
          break;
        }
        }
      }

      /// Estimate inputs/outputs to this function.
      unsigned TotalParamSize = 0;
      unsigned NumPtrInputs = 0;

      // Estimate using first occurrence.
      UniqueInputOperands.clear();
      for (Input &In : Data.InputSeq) {
        Instruction *I = OM.getInstr(FirstOccur + In.InstrNo);

        // Check for a function call being turned into a call
        //  to a function pointer.
        CallSite CS(I);
        if (CS && In.OpNo == CS.getNumArgOperands())
          NewFunctionCost += TargetTransformInfo::TCC_Basic;

        Value *IOp = I->getOperand(In.OpNo);
        // Add the operand to the unique set for the call.
        bool Inserted = UniqueInputOperands.insert(IOp).second;
        if (!Inserted)
          continue;
        // Check for a pointer that will need to be materialized.
        Type *IOpTy = IOp->getType();
        if (IOpTy->isPointerTy())
          ++NumPtrInputs;
        // Keep track of the total size of the inputs to the outlined
        //  function, we will use this for the cost of the call itself.
        TotalParamSize += getTypeSize(*Layout, IOpTy, WidestRegister);

        // Constant operands may have additional cost.
        bool HasFreeAddressComp = TTI.getAddressComputationCost(IOpTy) == 0;
        Constant *COp = dyn_cast<Constant>(IOp);
        if (COp && !HasFreeAddressComp)
          ChainCost -= getGlobalValueCost(COp);
      }

      /// The new function contains one instance of the chain of instructions.
      NewFunctionCost += ChainCost;
      // Add the cost of constant materialization.
      NewFunctionCost += MaterializedValues.size();

      /// Add the cost for each output.
      unsigned CostFromReLoad = 0;
      for (size_t OutputIdx : Data.Outputs) {
        Type *ParamEleTy = OM.getInstr(FirstOccur + OutputIdx)->getType();
        unsigned EstCost =
            getRegisterUsage(*Layout, ParamEleTy, WidestRegister);

        /// There will be a store into this variable in the outlined function.
        NewFunctionCost += EstCost;

        /// Each output value has a reload in the parent function.
        /// NOTE: This isn't entirely true if a specific instance doesn't use
        /// the value.
        CostFromReLoad += EstCost;
      }

      // Estimate the number of registers used in the function call.
      unsigned NumCallRegisters = TotalParamSize / WidestRegister;
      unsigned NumRegisters = TTI.getNumberOfRegisters(false);

      /// A call is generated at each occurence.
      ///   = call instruction + prepare each parameter + reload outputs.
      CostPerOccurence += 1 + NumCallRegisters + CostFromReLoad;

      LLVM_DEBUG(dbgs() << "Inputs : " << Data.InputSeq.size() << "["
                        << UniqueInputOperands.size() << "]"
                        << "; Outputs : " << Data.Outputs.count() << "\n");
      LLVM_DEBUG(dbgs() << "Chain Cost : " << ChainCost << "\n");
      LLVM_DEBUG(dbgs() << "CostPerOccur : " << CostPerOccurence << "\n");

      // No possibility of benefit.
      if (CostPerOccurence >= ChainCost)
        continue;

      /// Add the cost of the constant input condensing.
      ///  Each of the fixups will likely result in an add instruction.
      for (ConstantCondenseInstance &CInst : Data.ConstInsts) {
        if (CInst.Cost == 0)
          continue;
        Input &I = CInst.InputSeqs.front();
        Value *Op = OM.getInstrOp(FirstOccur + I.InstrNo, I.OpNo);
        unsigned OpCost =
            getRegisterUsage(*Layout, Op->getType(), WidestRegister);
        NewFunctionCost += (CInst.Cost * OpCost);
      }

      // Penalize large amounts of materialized pointers.
      // There are likely to be a number of spills so we conservatively say
      //  that each new input will spill.
      if (NumPtrInputs > NumRegisters)
        NewFunctionCost += NumRegisters + (NumPtrInputs - NumRegisters);

      // Compute the benefit of the chain and each occurrence.
      OC.BenefitPerOccur = ChainCost - CostPerOccurence;
      unsigned OutlineBenefit = OC.BenefitPerOccur * NumOccurences;

      // Outline cost statistics.
      LLVM_DEBUG(dbgs() << "BenefitPerOccur : " << OC.BenefitPerOccur << "\n");
      LLVM_DEBUG(dbgs() << "NewFunctionCost : " << NewFunctionCost << "\n");
      LLVM_DEBUG(dbgs() << "ParameterCost : " << NumCallRegisters << "\n");

      // No benefit.
      if (OutlineBenefit <= NewFunctionCost)
        continue;

      // As a final step we add in estimations for register pressure. We do
      //  this last because it can be costly to compute and is unnecessary
      //  if the candidate is already not going to be profitable.
      unsigned RegisterCost = computeOutlinedFunctionRegisterCost(OC);

      // We have extra setup and save cost if we preserve the frame pointer.
      bool ElimNonLeaf =
          FirstOccurFn->hasFnAttribute("no-frame-pointer-elim-non-leaf");
      bool NeedsFramePointer = false;
      // Check for non leaf frame pointer elim.
      if (ElimNonLeaf)
        NeedsFramePointer = ContainsCall;
      // Check for leaf frame pointer elim.
      else if (FirstOccurFn->hasFnAttribute("no-frame-pointer-elim")) {
        Attribute Attr = FirstOccurFn->getFnAttribute("no-frame-pointer-elim");
        NeedsFramePointer = Attr.getValueAsString() == "true";
      }
      // Accumulate the frame pointer cost.
      if (NeedsFramePointer)
        // save + register push/pop
        RegisterCost += 3;

      NewFunctionCost += RegisterCost;
      LLVM_DEBUG(dbgs() << "Estimated register cost : " << RegisterCost
                        << "\n");

      // No benefit.
      if (OutlineBenefit <= NewFunctionCost)
        continue;

      Data.NumCallRegisters = NumCallRegisters;
      OC.Benefit = OutlineBenefit - NewFunctionCost;

      // Less than desired benefit.
      if (OC.Benefit < MinBenefit) {
        OC.invalidate();
        continue;
      }
    }
  }

  unsigned computeOutlinedFunctionRegisterCost(OutlineCandidate &OC) {
    // Each 'key' in the map opens a new interval. The values
    // of the map are the index of the 'last seen' usage of the
    // instruction that is the key.
    typedef DenseMap<unsigned, unsigned> IntervalMap;
    // Marks the end of each interval.
    IntervalMap EndPoint;
    // Saves the list of instruction indices that are used in the loop.
    SmallSet<unsigned, 8> Ends;

    unsigned FirstOccur = *OC.begin();
    for (unsigned i = 0, InstIdx = FirstOccur; i < OC.Len; ++i, ++InstIdx) {
      // Save the end location of each USE.
      InstructionInfo &II = OM.getInstrInfo(InstIdx);
      for (unsigned InputIdx : II.InputIndexes) {
        // 0 denotes a constant or external input.
        if (InputIdx == 0)
          continue;
        EndPoint[InputIdx] = i;
        Ends.insert(InputIdx);
      }
    }

    // Saves the list of intervals that end with the index in 'key'.
    typedef SmallVector<unsigned, 2> InstrList;
    DenseMap<unsigned, InstrList> TransposeEnds;

    // Transpose the EndPoints to a list of values that end at each index.
    for (auto &Interval : EndPoint)
      TransposeEnds[Interval.second].push_back(Interval.first);

    Function *F = OM.getInstrFunction(*OC.begin());
    TargetTransformInfo &TTI = GetTTI(*F);
    unsigned WidestRegister = TTI.getRegisterBitWidth(false);
    unsigned NumRegisters = TTI.getNumberOfRegisters(false);
    unsigned SpillCount = 0;
    SmallSet<Instruction *, 8> OpenIntervals;
    for (unsigned i = 0, InstIdx = FirstOccur; i < OC.Len; ++i, ++InstIdx) {
      // Remove all of the instructions that end at this location.
      InstrList &List = TransposeEnds[i];
      for (unsigned ToRemove : List)
        OpenIntervals.erase(OM.getInstr(ToRemove));

      InstructionInfo &II = OM.getInstrInfo(InstIdx);
      if (II.Cost == TargetTransformInfo::TCC_Free)
        continue;

      // Count the number of live intervals.
      unsigned LiveIntervals = 0;
      for (auto Inst : OpenIntervals)
        LiveIntervals +=
            getRegisterUsage(*Layout, Inst->getType(), WidestRegister);

      // Check for spills.
      if (LiveIntervals > NumRegisters) {
        SpillCount += LiveIntervals - NumRegisters;
        for (unsigned i = 0, e = LiveIntervals - NumRegisters; i < e; ++i)
          OpenIntervals.erase(*OpenIntervals.begin());
      }

      // Add the current instruction to the list of open intervals.
      OpenIntervals.insert(OM.getInstr(InstIdx));
    }
    return SpillCount;
  }

  void computeOutlineCallRegisterCost() {
    DenseMap<BasicBlock *, std::set<unsigned>> BBsToCompute;
    DenseMap<unsigned, unsigned> OccurToUsage;

    // Collect all of the occurrences and blocks that need to have their
    //  usages computed.
    for (OutlineCandidate &OC : CandidateList) {
      if (!OC.isValid())
        continue;
      for (unsigned Occur : OC) {
        BasicBlock *Par = OM.getInstr(Occur)->getParent();
        BBsToCompute[Par].insert(Occur);
      }
    }

    // Nothing to compute.
    if (BBsToCompute.empty())
      return;

    // Each 'key' in the map opens a new interval. The values
    // of the map are the index of the 'last seen' usage of the
    // instruction that is the key.
    typedef DenseMap<Instruction *, Instruction *> IntervalMap;
    // Marks the end of each interval.
    IntervalMap EndPoint;

    BasicBlock *FirstBB = BBsToCompute.begin()->first;
    TargetTransformInfo &TTI = GetTTI(*FirstBB->getParent());
    unsigned WidestRegister = TTI.getRegisterBitWidth(false);
    unsigned NumRegisters = TTI.getNumberOfRegisters(false);

    // Perform a similar register cost to computeOutlinedFunctionRegisterCost.
    SmallSetVector<Instruction *, 8> BBInsts;
    SmallPtrSet<Value *, 8> BBLiveins;
    for (auto &BBPair : BBsToCompute) {
      // Reset previous usage.
      EndPoint.clear();
      BBInsts.clear();
      BBLiveins.clear();

      // Collect the instructions in this block that we want to compute usages
      // for.
      BasicBlock *Par = BBPair.first;
      for (unsigned Occur : BBPair.second)
        BBInsts.insert(OM.getInstr(Occur));
      Instruction *FarthestInstr = BBInsts.back();
      auto BBE = FarthestInstr->getIterator();
      ++BBE;

      // Build the live ranges for the instructions in the block.
      for (auto BBI = Par->begin(); BBI != BBE; ++BBI) {
        // Add the liveins to the occurrence usage.
        for (Value *Op : BBI->operands()) {
          Instruction *IOp = dyn_cast<Instruction>(Op);
          if (IOp && IOp->getParent() == Par)
            EndPoint[IOp] = &*BBI;
        }
      }

      // Saves the list of intervals that end with the index in 'key'.
      typedef SmallVector<Instruction *, 2> InstrList;
      DenseMap<Instruction *, InstrList> TransposeEnds;

      // Remove the instructions that are live out.
      for (auto BBI = Par->begin(); BBI != BBE; ++BBI)
        if (BBI->isUsedOutsideOfBlock(Par))
          EndPoint.erase(&*BBI);

      // Transpose the EndPoints to a list of values that end at each index.
      for (auto &Interval : EndPoint)
        TransposeEnds[Interval.second].push_back(Interval.first);

      SmallSet<Instruction *, 8> OpenIntervals;
      for (auto BBI = Par->begin(); BBI != BBE; ++BBI) {
        Instruction *I = &*BBI;

        // Remove all of the instructions that end at this location.
        InstrList &List = TransposeEnds[I];
        for (Instruction *ToRemove : List)
          OpenIntervals.erase(ToRemove);

        // Small helper lambda for computing the register usage.
        auto GetRegUsage = [&]() {
          unsigned RegUsage = 0;
          for (auto Inst : OpenIntervals)
            RegUsage +=
                getRegisterUsage(*Layout, Inst->getType(), WidestRegister);
          return RegUsage;
        };

        // Count the number of live intervals.
        if (BBInsts.count(I))
          OccurToUsage[OM.getInstrIdx(I)] += GetRegUsage();

        // Add the current instruction to the list of open intervals.
        if (!I->use_empty())
          OpenIntervals.insert(I);
      }
    }

    LLVM_DEBUG(dbgs() << "\n * Estimating spill cost per occurrence *\n");
    LLVM_DEBUG(dbgs() << " - Num Registers : " << NumRegisters << "\n");
    unsigned ViableRegisters = NumRegisters;

    // After we have the usages we rewalk the outline candidates and
    //  incorporate that info into the cost model.
    for (OutlineCandidate &OC : CandidateList) {
      if (!OC.isValid())
        continue;
      LLVM_DEBUG(dbgs() << "\nCandidate : " << OC.ID << "\n");
      AdditionalCandidateData &Data = OM.getCandidateData(OC);
      unsigned NumOutputs = Data.Outputs.count();
      for (unsigned i = 0, e = OC.size(); i < e; ++i) {
        unsigned Occur = OC.getOccurrence(i);
        // Get the max usage for the beginning of this call.
        unsigned Usage = OccurToUsage[Occur];

        // Add in the liveins from function parameters.
        BBLiveins.clear();
        Instruction *OccurI = OM.getInstr(Occur);
        BasicBlock *OccurPar = OccurI->getParent();
        for (Input &In : Data.InputSeq) {
          Value *Op = OM.getInstrOp(Occur + In.InstrNo, In.OpNo);
          Instruction *IOp = dyn_cast<Instruction>(Op);
          if (IOp && IOp->getParent() != OccurPar)
            if (BBLiveins.insert(IOp).second)
              ++Usage;
        }

        // Estimate any spills.
        unsigned TotalUsage = Usage + NumOutputs + Data.NumCallRegisters;
        unsigned Cost = 0;
        if (TotalUsage > ViableRegisters)
          Cost = TotalUsage - ViableRegisters;

        LLVM_DEBUG(dbgs() << "Occur " << i << "\n");
        LLVM_DEBUG(dbgs() << " - Usage : " << Usage << "\n");
        LLVM_DEBUG(dbgs() << " - Call Registers : " << Data.NumCallRegisters
                          << "\n");
        LLVM_DEBUG(dbgs() << " - Outputs : " << NumOutputs << "\n");
        LLVM_DEBUG(dbgs() << " - Cost : " << Cost << "\n");

        if (OC.Benefit <= Cost) {
          OC.invalidate();
          break;
        }
        OC.Benefit -= Cost;
      }
    }
  }

  /// Mapper containing information for the current module.
  IROutlinerMapper &OM;
  /// Our current list of candidates.
  std::vector<OutlineCandidate> &CandidateList;
  /// Functor for getting the target information for a function.
  function_ref<TargetTransformInfo &(Function &)> GetTTI;
  /// Current Module data layout.
  const DataLayout *Layout;
};

// \brief Outline all of the profitable candidates.
void outlineCandidates(MutableArrayRef<OutlineCandidate> CL,
                       IROutlinerMapper &OM, bool HasProfileData) {
  FunctionSplicer FS(HasProfileData);
  for (const OutlineCandidate &OC : CL) {
    if (!OC.isValid())
      continue;
    ++NumCandidatesOutlined;

    // Prepare->Outline->Finalize
    FS.prepareForNewCandidate(OC, OM);
    for (unsigned Occur : OC)
      FS.outlineOccurrence(OC, Occur, OM);
    FS.finalize(OC, OM);
  }
}

// Run the outliner over the provided module /p M.
bool runImpl(Module &M, ProfileSummaryInfo *PSI,
             function_ref<BlockFrequencyInfo &(Function &)> GetBFI,
             function_ref<TargetTransformInfo &(Function &)> GetTTI) {
  IROutlinerMapper OM;
  std::vector<unsigned> CCVec = llvm::mapIRModule(OM, M, PSI, GetBFI);
  OM.initAdditionalData();

  // No potential candidates.
  if (CCVec.size() < MinOccurrences * MinInstructionLength)
    return false;

  // Pre prune functor for any known unprofitable candidates.
  std::function<bool(ArrayRef<unsigned>, unsigned)> PrePruneFn =
      [&](ArrayRef<unsigned> Occurs, unsigned Len) {
        if (Len != 1)
          return false;
        Instruction *I = OM.getInstr(Occurs[0]);
        // Empty function call.
        if (CallSite CS = CallSite(I))
          return CS.getCalledFunction() && CS.getNumArgOperands() == 0;
        // Non constant operation.
        return none_of(I->operand_values(),
                       [](Value *V) { return isa<Constant>(V); });
      };

  // Find outlining candidates.
  std::vector<OutlineCandidate> CL = findSequentialOutliningCandidates(
      PrePruneFn, CCVec, MinInstructionLength, MinOccurrences);
  if (CL.empty())
    return false;

  // Analyze candidate profitability.
  OutlinerAnalysis OAI(OM, CL, GetTTI, &M.getDataLayout());
  OAI.analyzeCandidateList();

  // Prune any overlaps.
  if (!pruneSequentialOutlineCandidateList(CL, OM.getNumMappedInstructions()))
    return false;

  // Outline the profitable candidates.
  outlineCandidates(CL, OM, PSI->hasProfileSummary());
  return true;
}
} // namespace

PreservedAnalyses CodeSizeOutlinerPass::run(Module &M,
                                            ModuleAnalysisManager &AM) {
  auto &FAM = AM.getResult<FunctionAnalysisManagerModuleProxy>(M).getManager();
  std::function<TargetTransformInfo &(Function &)> GetTTI =
      [&](Function &F) -> TargetTransformInfo & {
    return FAM.getResult<TargetIRAnalysis>(F);
  };
  std::function<BlockFrequencyInfo &(Function &)> GetBFI =
      [&](Function &F) -> BlockFrequencyInfo & {
    return FAM.getResult<BlockFrequencyAnalysis>(F);
  };
  ProfileSummaryInfo *PSI = &AM.getResult<ProfileSummaryAnalysis>(M);
  return runImpl(M, PSI, GetBFI, GetTTI) ? PreservedAnalyses::none()
                                         : PreservedAnalyses::all();
}

struct CodeSizeOutlinerLegacyPass : public ModulePass {
  static char ID; // Pass identification, replacement for typeid
  CodeSizeOutlinerLegacyPass() : ModulePass(ID) {
    initializeCodeSizeOutlinerLegacyPassPass(*PassRegistry::getPassRegistry());
  }
  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<ProfileSummaryInfoWrapperPass>();
    AU.addRequired<TargetTransformInfoWrapperPass>();
  }
  bool runOnModule(Module &M) override {
    if (skipModule(M))
      return false;
    TargetTransformInfoWrapperPass *TTIWP =
        &getAnalysis<TargetTransformInfoWrapperPass>();
    DenseMap<Function *, TargetTransformInfo> TTIMap;
    std::function<TargetTransformInfo &(Function &)> GetTTI =
        [&](Function &F) -> TargetTransformInfo & {
      auto TTIIt = TTIMap.find(&F);
      if (TTIIt == TTIMap.end())
        TTIIt = TTIMap.try_emplace(&F, std::move(TTIWP->getTTI(F))).first;
      return TTIIt->second;
    };
    std::unique_ptr<BlockFrequencyInfo> CurBFI;
    std::function<BlockFrequencyInfo &(Function &)> GetBFI =
        [&](Function &F) -> BlockFrequencyInfo & {
      DominatorTree DT(F);
      LoopInfo LI(DT);
      BranchProbabilityInfo BPI(F, LI);
      CurBFI.reset(new BlockFrequencyInfo(F, BPI, LI));
      return *CurBFI.get();
    };
    ProfileSummaryInfo *PSI =
        getAnalysis<ProfileSummaryInfoWrapperPass>().getPSI();
    return runImpl(M, PSI, GetBFI, GetTTI);
  }
};

char CodeSizeOutlinerLegacyPass::ID = 0;
INITIALIZE_PASS_BEGIN(CodeSizeOutlinerLegacyPass, DEBUG_TYPE,
                      "Code Size Outliner", false, false)
INITIALIZE_PASS_DEPENDENCY(ProfileSummaryInfoWrapperPass)
INITIALIZE_PASS_DEPENDENCY(TargetTransformInfoWrapperPass)
INITIALIZE_PASS_END(CodeSizeOutlinerLegacyPass, DEBUG_TYPE,
                    "Code Size Outliner", false, false)
ModulePass *llvm::createCodeSizeOutlinerPass() {
  return new CodeSizeOutlinerLegacyPass();
}
