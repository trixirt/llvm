//===---- MachineOutliner.cpp - Outline instructions -----------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
///
/// \file
/// Replaces repeated sequences of instructions with function calls.
///
/// This works by placing every instruction from every basic block in a
/// suffix tree, and repeatedly querying that tree for repeated sequences of
/// instructions. If a sequence of instructions appears often, then it ought
/// to be beneficial to pull out into a function.
///
/// The MachineOutliner communicates with a given target using hooks defined in
/// TargetInstrInfo.h. The target supplies the outliner with information on how
/// a specific sequence of instructions should be outlined. This information
/// is used to deduce the number of instructions necessary to
///
/// * Create an outlined function
/// * Call that outlined function
///
/// Targets must implement
///   * getOutliningCandidateInfo
///   * buildOutlinedFrame
///   * insertOutlinedCall
///   * isFunctionSafeToOutlineFrom
///
/// in order to make use of the MachineOutliner.
///
/// This was originally presented at the 2016 LLVM Developers' Meeting in the
/// talk "Reducing Code Size Using Outlining". For a high-level overview of
/// how this pass works, the talk is available on YouTube at
///
/// https://www.youtube.com/watch?v=yorld-WSOeU
///
/// The slides for the talk are available at
///
/// http://www.llvm.org/devmtg/2016-11/Slides/Paquette-Outliner.pdf
///
/// The talk provides an overview of how the outliner finds candidates and
/// ultimately outlines them. It describes how the main data structure for this
/// pass, the suffix tree, is queried and purged for candidates. It also gives
/// a simplified suffix tree construction algorithm for suffix trees based off
/// of the algorithm actually used here, Ukkonen's algorithm.
///
/// For the original RFC for this pass, please see
///
/// http://lists.llvm.org/pipermail/llvm-dev/2016-August/104170.html
///
/// For more information on the suffix tree data structure, please see
/// https://www.cs.helsinki.fi/u/ukkonen/SuffixT1withFigs.pdf
///
//===----------------------------------------------------------------------===//
#include "llvm/CodeGen/InstructionMapper.h"
#include "llvm/CodeGen/MachineOutliner.h"
#include "llvm/ADT/SuffixTree.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/Twine.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineModuleInfo.h"
#include "llvm/CodeGen/MachineOptimizationRemarkEmitter.h"
#include "llvm/CodeGen/MachineRegisterInfo.h"
#include "llvm/CodeGen/Passes.h"
#include "llvm/CodeGen/TargetInstrInfo.h"
#include "llvm/CodeGen/TargetSubtargetInfo.h"
#include "llvm/IR/DIBuilder.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Mangler.h"
#include "llvm/Support/Allocator.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include <functional>
#include <map>
#include <sstream>
#include <tuple>
#include <vector>

#define DEBUG_TYPE "machine-outliner"

using namespace llvm;
using namespace ore;
using namespace outliner;

STATISTIC(NumOutlined, "Number of candidates outlined");
STATISTIC(FunctionsCreated, "Number of functions created");

// Set to true if the user wants the outliner to run on linkonceodr linkage
// functions. This is false by default because the linker can dedupe linkonceodr
// functions. Since the outliner is confined to a single module (modulo LTO),
// this is off by default. It should, however, be the default behaviour in
// LTO.
static cl::opt<bool> EnableLinkOnceODROutlining(
    "enable-linkonceodr-outlining",
    cl::Hidden,
    cl::desc("Enable the machine outliner on linkonceodr functions"),
    cl::init(false));

namespace {

/// An interprocedural pass which finds repeated sequences of
/// instructions and replaces them with calls to functions.
///
/// Each instruction is mapped to an unsigned integer and placed in a string.
/// The resulting mapping is then placed in a \p SuffixTree. The \p SuffixTree
/// is then repeatedly queried for repeated sequences of instructions. Each
/// non-overlapping repeated sequence is then placed in its own
/// \p MachineFunction and each instance is then replaced with a call to that
/// function.
struct MachineOutliner : public ModulePass {

  static char ID;

  /// Set to true if the outliner should consider functions with
  /// linkonceodr linkage.
  bool OutlineFromLinkOnceODRs = false;

  /// Set to true if the outliner should run on all functions in the module
  /// considered safe for outlining.
  /// Set to true by default for compatibility with llc's -run-pass option.
  /// Set when the pass is constructed in TargetPassConfig.
  bool RunOnAllFunctions = true;

  // Collection of IR functions created by the outliner.
  std::vector<Function *> CreatedIRFunctions;

  StringRef getPassName() const override { return "Machine Outliner"; }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<MachineModuleInfo>();
    AU.addPreserved<MachineModuleInfo>();
    AU.setPreservesAll();
    ModulePass::getAnalysisUsage(AU);
  }

  MachineOutliner() : ModulePass(ID) {
    initializeMachineOutlinerPass(*PassRegistry::getPassRegistry());
  }

  /// Remark output explaining that not outlining a set of candidates would be
  /// better than outlining that set.
  void emitNotOutliningCheaperRemark(
      unsigned StringLen, std::vector<Candidate> &CandidatesForRepeatedSeq,
      OutlinedFunction &OF);

  /// Remark output explaining that a function was outlined.
  void emitOutlinedFunctionRemark(OutlinedFunction &OF);

  using InstructionMapperType =
    InstructionMapper<MachineBasicBlock, MachineInstr, MachineInstrExpressionTrait>;
  

  /// Find all repeated substrings that satisfy the outlining cost model.
  ///
  /// If a substring appears at least twice, then it must be represented by
  /// an internal node which appears in at least two suffixes. Each suffix
  /// is represented by a leaf node. To do this, we visit each internal node
  /// in the tree, using the leaf children of each internal node. If an
  /// internal node represents a beneficial substring, then we use each of
  /// its leaf children to find the locations of its substring.
  ///
  /// \param ST A suffix tree to query.
  /// \param Mapper Contains outlining mapping information.
  /// \param[out] CandidateList Filled with candidates representing each
  /// beneficial substring.
  /// \param[out] FunctionList Filled with a list of \p OutlinedFunctions
  /// each type of candidate.
  ///
  /// \returns The length of the longest candidate found.
  unsigned
  findCandidates(SuffixTree &ST,
		 InstructionMapperType &Mapper,
                 std::vector<std::shared_ptr<Candidate>> &CandidateList,
                 std::vector<OutlinedFunction> &FunctionList);

  /// Replace the sequences of instructions represented by the
  /// \p Candidates in \p CandidateList with calls to \p MachineFunctions
  /// described in \p FunctionList.
  ///
  /// \param M The module we are outlining from.
  /// \param CandidateList A list of candidates to be outlined.
  /// \param FunctionList A list of functions to be inserted into the module.
  /// \param Mapper Contains the instruction mappings for the module.
  bool outline(Module &M,
               const ArrayRef<std::shared_ptr<Candidate>> &CandidateList,
               std::vector<OutlinedFunction> &FunctionList,
	       InstructionMapperType &Mapper);

  /// Creates a function for \p OF and inserts it into the module.
  MachineFunction *createOutlinedFunction(Module &M, const OutlinedFunction &OF,
					  InstructionMapperType &Mapper);

  /// Find potential outlining candidates and store them in \p CandidateList.
  ///
  /// For each type of potential candidate, also build an \p OutlinedFunction
  /// struct containing the information to build the function for that
  /// candidate.
  ///
  /// \param[out] CandidateList Filled with outlining candidates for the module.
  /// \param[out] FunctionList Filled with functions corresponding to each type
  /// of \p Candidate.
  /// \param ST The suffix tree for the module.
  ///
  /// \returns The length of the longest candidate found. 0 if there are none.
  unsigned
  buildCandidateList(std::vector<std::shared_ptr<Candidate>> &CandidateList,
                     std::vector<OutlinedFunction> &FunctionList,
                     SuffixTree &ST, InstructionMapperType &Mapper);

  /// Helper function for pruneOverlaps.
  /// Removes \p C from the candidate list, and updates its \p OutlinedFunction.
  void prune(Candidate &C, std::vector<OutlinedFunction> &FunctionList);

  /// Remove any overlapping candidates that weren't handled by the
  /// suffix tree's pruning method.
  ///
  /// Pruning from the suffix tree doesn't necessarily remove all overlaps.
  /// If a short candidate is chosen for outlining, then a longer candidate
  /// which has that short candidate as a suffix is chosen, the tree's pruning
  /// method will not find it. Thus, we need to prune before outlining as well.
  ///
  /// \param[in,out] CandidateList A list of outlining candidates.
  /// \param[in,out] FunctionList A list of functions to be outlined.
  /// \param Mapper Contains instruction mapping info for outlining.
  /// \param MaxCandidateLen The length of the longest candidate.
  void pruneOverlaps(std::vector<std::shared_ptr<Candidate>> &CandidateList,
                     std::vector<OutlinedFunction> &FunctionList,
		     InstructionMapperType &Mapper,
                     unsigned MaxCandidateLen);

  /// Construct a suffix tree on the instructions in \p M and outline repeated
  /// strings from that tree.
  bool runOnModule(Module &M) override;

  /// Return a DISubprogram for OF if one exists, and null otherwise. Helper
  /// function for remark emission.
  DISubprogram *getSubprogramOrNull(const OutlinedFunction &OF) {
    DISubprogram *SP;
    for (const std::shared_ptr<Candidate> &C : OF.Candidates)
      if (C && C->getMF() && (SP = C->getMF()->getFunction().getSubprogram()))
        return SP;
    return nullptr;
  }
};

} // Anonymous namespace.

char MachineOutliner::ID = 0;

namespace llvm {
ModulePass *createMachineOutlinerPass(bool RunOnAllFunctions) {
  MachineOutliner *OL = new MachineOutliner();
  OL->RunOnAllFunctions = RunOnAllFunctions;
  return OL;
}

} // namespace llvm

INITIALIZE_PASS(MachineOutliner, DEBUG_TYPE, "Machine Function Outliner", false,
                false)

void MachineOutliner::emitNotOutliningCheaperRemark(
    unsigned StringLen, std::vector<Candidate> &CandidatesForRepeatedSeq,
    OutlinedFunction &OF) {
  Candidate &C = CandidatesForRepeatedSeq.front();
  MachineOptimizationRemarkEmitter MORE(*(C.getMF()), nullptr);
  MORE.emit([&]() {
    MachineOptimizationRemarkMissed R(DEBUG_TYPE, "NotOutliningCheaper",
                                      C.front()->getDebugLoc(), C.getB());
    R << "Did not outline " << NV("Length", StringLen) << " instructions"
      << " from " << NV("NumOccurrences", CandidatesForRepeatedSeq.size())
      << " locations."
      << " Bytes from outlining all occurrences ("
      << NV("OutliningCost", OF.getOutliningCost()) << ")"
      << " >= Unoutlined instruction bytes ("
      << NV("NotOutliningCost", OF.getNotOutlinedCost()) << ")"
      << " (Also found at: ";

    // Tell the user the other places the candidate was found.
    for (unsigned i = 1, e = CandidatesForRepeatedSeq.size(); i < e; i++) {
      R << NV((Twine("OtherStartLoc") + Twine(i)).str(),
              CandidatesForRepeatedSeq[i].front()->getDebugLoc());
      if (i != e - 1)
        R << ", ";
    }

    R << ")";
    return R;
  });
}

void MachineOutliner::emitOutlinedFunctionRemark(OutlinedFunction &OF) {
  MachineBasicBlock *MBB = &*OF.MF->begin();
  MachineOptimizationRemarkEmitter MORE(*OF.MF, nullptr);
  MachineOptimizationRemark R(DEBUG_TYPE, "OutlinedFunction",
                              MBB->findDebugLoc(MBB->begin()), MBB);
  R << "Saved " << NV("OutliningBenefit", OF.getBenefit()) << " bytes by "
    << "outlining " << NV("Length", OF.Sequence.size()) << " instructions "
    << "from " << NV("NumOccurrences", OF.getOccurrenceCount())
    << " locations. "
    << "(Found at: ";

  // Tell the user the other places the candidate was found.
  for (size_t i = 0, e = OF.Candidates.size(); i < e; i++) {

    // Skip over things that were pruned.
    if (!OF.Candidates[i]->InCandidateList)
      continue;

    R << NV((Twine("StartLoc") + Twine(i)).str(),
            OF.Candidates[i]->front()->getDebugLoc());
    if (i != e - 1)
      R << ", ";
  }

  R << ")";

  MORE.emit(R);
}

unsigned MachineOutliner::findCandidates(
    SuffixTree &ST, InstructionMapperType &Mapper,
    std::vector<std::shared_ptr<Candidate>> &CandidateList,
    std::vector<OutlinedFunction> &FunctionList) {
  CandidateList.clear();
  FunctionList.clear();
  unsigned MaxLen = 0;

  // FIXME: Visit internal nodes instead of leaves.
  for (SuffixTreeNode *Leaf : ST.LeafVector) {
    assert(Leaf && "Leaves in LeafVector cannot be null!");
    if (!Leaf->IsInTree)
      continue;

    assert(Leaf->Parent && "All leaves must have parents!");
    SuffixTreeNode &Parent = *(Leaf->Parent);

    // If it doesn't appear enough, or we already outlined from it, skip it.
    if (Parent.OccurrenceCount < 2 || Parent.isRoot() || !Parent.IsInTree)
      continue;

    // Figure out if this candidate is beneficial.
    unsigned StringLen = Leaf->ConcatLen - (unsigned)Leaf->size();

    // Too short to be beneficial; skip it.
    // FIXME: This isn't necessarily true for, say, X86. If we factor in
    // instruction lengths we need more information than this.
    if (StringLen < 2)
      continue;

    // If this is a beneficial class of candidate, then every one is stored in
    // this vector.
    std::vector<Candidate> CandidatesForRepeatedSeq;

    // Figure out the call overhead for each instance of the sequence.
    for (auto &ChildPair : Parent.Children) {
      SuffixTreeNode *M = ChildPair.second;

      if (M && M->IsInTree && M->isLeaf()) {
        // Never visit this leaf again.
        M->IsInTree = false;
        unsigned StartIdx = M->SuffixIdx;
        unsigned EndIdx = StartIdx + StringLen - 1;

        // Trick: Discard some candidates that would be incompatible with the
        // ones we've already found for this sequence. This will save us some
        // work in candidate selection.
        //
        // If two candidates overlap, then we can't outline them both. This
        // happens when we have candidates that look like, say
        //
        // AA (where each "A" is an instruction).
        //
        // We might have some portion of the module that looks like this:
        // AAAAAA (6 A's)
        //
        // In this case, there are 5 different copies of "AA" in this range, but
        // at most 3 can be outlined. If only outlining 3 of these is going to
        // be unbeneficial, then we ought to not bother.
        //
        // Note that two things DON'T overlap when they look like this:
        // start1...end1 .... start2...end2
        // That is, one must either
        // * End before the other starts
        // * Start after the other ends
        if (std::all_of(CandidatesForRepeatedSeq.begin(),
                        CandidatesForRepeatedSeq.end(),
                        [&StartIdx, &EndIdx](const Candidate &C) {
                          return (EndIdx < C.getStartIdx() ||
                                  StartIdx > C.getEndIdx());
                        })) {
          // It doesn't overlap with anything, so we can outline it.
          // Each sequence is over [StartIt, EndIt].
          // Save the candidate and its location.

          MachineBasicBlock::iterator StartIt = Mapper.InstrList[StartIdx];
          MachineBasicBlock::iterator EndIt = Mapper.InstrList[EndIdx];

          CandidatesForRepeatedSeq.emplace_back(StartIdx, StringLen, StartIt,
                                                EndIt, StartIt->getParent(),
                                                FunctionList.size());
        }
      }
    }

    // We've found something we might want to outline.
    // Create an OutlinedFunction to store it and check if it'd be beneficial
    // to outline.
    if (CandidatesForRepeatedSeq.empty())
      continue;

    // Arbitrarily choose a TII from the first candidate.
    // FIXME: Should getOutliningCandidateInfo move to TargetMachine?
    const TargetInstrInfo *TII =
        CandidatesForRepeatedSeq[0].getMF()->getSubtarget().getInstrInfo();

    OutlinedFunction OF =
        TII->getOutliningCandidateInfo(CandidatesForRepeatedSeq);

    // If we deleted every candidate, then there's nothing to outline.
    if (OF.Candidates.empty())
      continue;

    std::vector<unsigned> Seq;
    for (unsigned i = Leaf->SuffixIdx; i < Leaf->SuffixIdx + StringLen; i++)
      Seq.push_back(ST.Str[i]);
    OF.Sequence = Seq;
    OF.Name = FunctionList.size();

    // Is it better to outline this candidate than not?
    if (OF.getBenefit() < 1) {
      emitNotOutliningCheaperRemark(StringLen, CandidatesForRepeatedSeq, OF);
      continue;
    }

    if (StringLen > MaxLen)
      MaxLen = StringLen;

    // The function is beneficial. Save its candidates to the candidate list
    // for pruning.
    for (std::shared_ptr<Candidate> &C : OF.Candidates)
      CandidateList.push_back(C);
    FunctionList.push_back(OF);

    // Move to the next function.
    Parent.IsInTree = false;
  }

  return MaxLen;
}

// Remove C from the candidate space, and update its OutlinedFunction.
void MachineOutliner::prune(Candidate &C,
                            std::vector<OutlinedFunction> &FunctionList) {
  // Get the OutlinedFunction associated with this Candidate.
  OutlinedFunction &F = FunctionList[C.FunctionIdx];

  // Update C's associated function's occurrence count.
  F.decrement();

  // Remove C from the CandidateList.
  C.InCandidateList = false;

  LLVM_DEBUG(dbgs() << "- Removed a Candidate \n";
             dbgs() << "--- Num fns left for candidate: "
                    << F.getOccurrenceCount() << "\n";
             dbgs() << "--- Candidate's functions's benefit: " << F.getBenefit()
                    << "\n";);
}

void MachineOutliner::pruneOverlaps(
    std::vector<std::shared_ptr<Candidate>> &CandidateList,
    std::vector<OutlinedFunction> &FunctionList, InstructionMapperType &Mapper,
    unsigned MaxCandidateLen) {

  // Return true if this candidate became unbeneficial for outlining in a
  // previous step.
  auto ShouldSkipCandidate = [&FunctionList, this](Candidate &C) {

    // Check if the candidate was removed in a previous step.
    if (!C.InCandidateList)
      return true;

    // C must be alive. Check if we should remove it.
    if (FunctionList[C.FunctionIdx].getBenefit() < 1) {
      prune(C, FunctionList);
      return true;
    }

    // C is in the list, and F is still beneficial.
    return false;
  };

  // TODO: Experiment with interval trees or other interval-checking structures
  // to lower the time complexity of this function.
  // TODO: Can we do better than the simple greedy choice?
  // Check for overlaps in the range.
  // This is O(MaxCandidateLen * CandidateList.size()).
  for (auto It = CandidateList.begin(), Et = CandidateList.end(); It != Et;
       It++) {
    Candidate &C1 = **It;

    // If C1 was already pruned, or its function is no longer beneficial for
    // outlining, move to the next candidate.
    if (ShouldSkipCandidate(C1))
      continue;

    // The minimum start index of any candidate that could overlap with this
    // one.
    unsigned FarthestPossibleIdx = 0;

    // Either the index is 0, or it's at most MaxCandidateLen indices away.
    if (C1.getStartIdx() > MaxCandidateLen)
      FarthestPossibleIdx = C1.getStartIdx() - MaxCandidateLen;

    // Compare against the candidates in the list that start at most
    // FarthestPossibleIdx indices away from C1. There are at most
    // MaxCandidateLen of these.
    for (auto Sit = It + 1; Sit != Et; Sit++) {
      Candidate &C2 = **Sit;

      // Is this candidate too far away to overlap?
      if (C2.getStartIdx() < FarthestPossibleIdx)
        break;

      // If C2 was already pruned, or its function is no longer beneficial for
      // outlining, move to the next candidate.
      if (ShouldSkipCandidate(C2))
        continue;

      // Do C1 and C2 overlap?
      //
      // Not overlapping:
      // High indices... [C1End ... C1Start][C2End ... C2Start] ...Low indices
      //
      // We sorted our candidate list so C2Start <= C1Start. We know that
      // C2End > C2Start since each candidate has length >= 2. Therefore, all we
      // have to check is C2End < C2Start to see if we overlap.
      if (C2.getEndIdx() < C1.getStartIdx())
        continue;

      // C1 and C2 overlap.
      // We need to choose the better of the two.
      //
      // Approximate this by picking the one which would have saved us the
      // most instructions before any pruning.

      // Is C2 a better candidate?
      if (C2.Benefit > C1.Benefit) {
        // Yes, so prune C1. Since C1 is dead, we don't have to compare it
        // against anything anymore, so break.
        prune(C1, FunctionList);
        break;
      }

      // Prune C2 and move on to the next candidate.
      prune(C2, FunctionList);
    }
  }
}

unsigned MachineOutliner::buildCandidateList(
    std::vector<std::shared_ptr<Candidate>> &CandidateList,
    std::vector<OutlinedFunction> &FunctionList, SuffixTree &ST,
    InstructionMapperType &Mapper) {

  std::vector<unsigned> CandidateSequence; // Current outlining candidate.
  unsigned MaxCandidateLen = 0;            // Length of the longest candidate.

  MaxCandidateLen =
      findCandidates(ST, Mapper, CandidateList, FunctionList);

  // Sort the candidates in decending order. This will simplify the outlining
  // process when we have to remove the candidates from the mapping by
  // allowing us to cut them out without keeping track of an offset.
  std::stable_sort(
      CandidateList.begin(), CandidateList.end(),
      [](const std::shared_ptr<Candidate> &LHS,
         const std::shared_ptr<Candidate> &RHS) { return *LHS < *RHS; });

  return MaxCandidateLen;
}

MachineFunction *
MachineOutliner::createOutlinedFunction(Module &M, const OutlinedFunction &OF,
                                        InstructionMapperType &Mapper) {

  // Create the function name. This should be unique. For now, just hash the
  // module name and include it in the function name plus the number of this
  // function.
  std::ostringstream NameStream;
  NameStream << "OUTLINED_FUNCTION_" << OF.Name;

  // Create the function using an IR-level function.
  LLVMContext &C = M.getContext();
  Function *F = dyn_cast<Function>(
      M.getOrInsertFunction(NameStream.str(), Type::getVoidTy(C)));
  assert(F && "Function was null!");

  // NOTE: If this is linkonceodr, then we can take advantage of linker deduping
  // which gives us better results when we outline from linkonceodr functions.
  F->setLinkage(GlobalValue::InternalLinkage);
  F->setUnnamedAddr(GlobalValue::UnnamedAddr::Global);

  // FIXME: Set nounwind, so we don't generate eh_frame? Haven't verified it's
  // necessary.

  // Set optsize/minsize, so we don't insert padding between outlined
  // functions.
  F->addFnAttr(Attribute::OptimizeForSize);
  F->addFnAttr(Attribute::MinSize);

  // Save F so that we can add debug info later if we need to.
  CreatedIRFunctions.push_back(F);

  BasicBlock *EntryBB = BasicBlock::Create(C, "entry", F);
  IRBuilder<> Builder(EntryBB);
  Builder.CreateRetVoid();

  MachineModuleInfo &MMI = getAnalysis<MachineModuleInfo>();
  MachineFunction &MF = MMI.getOrCreateMachineFunction(*F);
  MachineBasicBlock &MBB = *MF.CreateMachineBasicBlock();
  const TargetSubtargetInfo &STI = MF.getSubtarget();
  const TargetInstrInfo &TII = *STI.getInstrInfo();

  // Insert the new function into the module.
  MF.insert(MF.begin(), &MBB);

  // Copy over the instructions for the function using the integer mappings in
  // its sequence.
  for (unsigned Str : OF.Sequence) {
    MachineInstr *NewMI =
        MF.CloneMachineInstr(Mapper.IntegerInstructionMap.find(Str)->second);
    NewMI->dropMemRefs(MF);

    // Don't keep debug information for outlined instructions.
    NewMI->setDebugLoc(DebugLoc());
    MBB.insert(MBB.end(), NewMI);
  }

  TII.buildOutlinedFrame(MBB, MF, OF);

  // If there's a DISubprogram associated with this outlined function, then
  // emit debug info for the outlined function.
  if (DISubprogram *SP = getSubprogramOrNull(OF)) {
    // We have a DISubprogram. Get its DICompileUnit.
    DICompileUnit *CU = SP->getUnit();
    DIBuilder DB(M, true, CU);
    DIFile *Unit = SP->getFile();
    Mangler Mg;

    // Walk over each IR function we created in the outliner and create
    // DISubprograms for each function.
    for (Function *F : CreatedIRFunctions) {
      // Get the mangled name of the function for the linkage name.
      std::string Dummy;
      llvm::raw_string_ostream MangledNameStream(Dummy);
      Mg.getNameWithPrefix(MangledNameStream, F, false);

      DISubprogram *SP = DB.createFunction(
          Unit /* Context */, F->getName(), StringRef(MangledNameStream.str()),
          Unit /* File */,
          0 /* Line 0 is reserved for compiler-generated code. */,
          DB.createSubroutineType(
              DB.getOrCreateTypeArray(None)), /* void type */
          false, true, 0, /* Line 0 is reserved for compiler-generated code. */
          DINode::DIFlags::FlagArtificial /* Compiler-generated code. */,
          true /* Outlined code is optimized code by definition. */);

      // Don't add any new variables to the subprogram.
      DB.finalizeSubprogram(SP);

      // Attach subprogram to the function.
      F->setSubprogram(SP);
    }

    // We're done with the DIBuilder.
    DB.finalize();
  }

  // Outlined functions shouldn't preserve liveness.
  MF.getProperties().reset(MachineFunctionProperties::Property::TracksLiveness);
  MF.getRegInfo().freezeReservedRegs(MF);
  return &MF;
}

bool MachineOutliner::outline(
    Module &M, const ArrayRef<std::shared_ptr<Candidate>> &CandidateList,
    std::vector<OutlinedFunction> &FunctionList, InstructionMapperType &Mapper) {

  bool OutlinedSomething = false;
  // Replace the candidates with calls to their respective outlined functions.
  for (const std::shared_ptr<Candidate> &Cptr : CandidateList) {
    Candidate &C = *Cptr;
    // Was the candidate removed during pruneOverlaps?
    if (!C.InCandidateList)
      continue;

    // If not, then look at its OutlinedFunction.
    OutlinedFunction &OF = FunctionList[C.FunctionIdx];

    // Was its OutlinedFunction made unbeneficial during pruneOverlaps?
    if (OF.getBenefit() < 1)
      continue;

    // Does this candidate have a function yet?
    if (!OF.MF) {
      OF.MF = createOutlinedFunction(M, OF, Mapper);
      emitOutlinedFunctionRemark(OF);
      FunctionsCreated++;
    }

    MachineFunction *MF = OF.MF;
    MachineBasicBlock &MBB = *C.getB();
    MachineBasicBlock::iterator StartIt = C.front();
    MachineBasicBlock::iterator EndIt = C.back();
    assert(StartIt != C.getB()->end() && "StartIt out of bounds!");
    assert(EndIt != C.getB()->end() && "EndIt out of bounds!");

    const TargetSubtargetInfo &STI = MF->getSubtarget();
    const TargetInstrInfo &TII = *STI.getInstrInfo();

    // Insert a call to the new function and erase the old sequence.
    auto CallInst = TII.insertOutlinedCall(M, MBB, StartIt, *OF.MF, C);

    // If the caller tracks liveness, then we need to make sure that anything
    // we outline doesn't break liveness assumptions.
    // The outlined functions themselves currently don't track liveness, but
    // we should make sure that the ranges we yank things out of aren't
    // wrong.
    if (MBB.getParent()->getProperties().hasProperty(
            MachineFunctionProperties::Property::TracksLiveness)) {
      // Helper lambda for adding implicit def operands to the call instruction.
      auto CopyDefs = [&CallInst](MachineInstr &MI) {
        for (MachineOperand &MOP : MI.operands()) {
          // Skip over anything that isn't a register.
          if (!MOP.isReg())
            continue;

          // If it's a def, add it to the call instruction.
          if (MOP.isDef())
            CallInst->addOperand(
                MachineOperand::CreateReg(MOP.getReg(), true, /* isDef = true */
                                          true /* isImp = true */));
        }
      };

      // Copy over the defs in the outlined range.
      // First inst in outlined range <-- Anything that's defined in this
      // ...                           .. range has to be added as an implicit
      // Last inst in outlined range  <-- def to the call instruction.
      std::for_each(CallInst, std::next(EndIt), CopyDefs);
    }

    // Erase from the point after where the call was inserted up to, and
    // including, the final instruction in the sequence.
    // Erase needs one past the end, so we need std::next there too.
    MBB.erase(std::next(StartIt), std::next(EndIt));
    OutlinedSomething = true;

    // Statistics.
    NumOutlined++;
  }

  LLVM_DEBUG(dbgs() << "OutlinedSomething = " << OutlinedSomething << "\n";);

  return OutlinedSomething;
}

bool MachineOutliner::runOnModule(Module &M) {
  // Check if there's anything in the module. If it's empty, then there's
  // nothing to outline.
  if (M.empty())
    return false;

  MachineModuleInfo &MMI = getAnalysis<MachineModuleInfo>();

  // If the user passed -enable-machine-outliner=always or
  // -enable-machine-outliner, the pass will run on all functions in the module.
  // Otherwise, if the target supports default outlining, it will run on all
  // functions deemed by the target to be worth outlining from by default. Tell
  // the user how the outliner is running.
  LLVM_DEBUG(
    dbgs() << "Machine Outliner: Running on ";
    if (RunOnAllFunctions)
      dbgs() << "all functions";
    else
      dbgs() << "target-default functions";
    dbgs() << "\n"
  );

  // If the user specifies that they want to outline from linkonceodrs, set
  // it here.
  OutlineFromLinkOnceODRs = EnableLinkOnceODROutlining;

  InstructionMapper<MachineBasicBlock, MachineInstr, MachineInstrExpressionTrait> Mapper;

  // Build instruction mappings for each function in the module. Start by
  // iterating over each Function in M.
  for (Function &F : M) {

    // If there's nothing in F, then there's no reason to try and outline from
    // it.
    if (F.empty())
      continue;

    // There's something in F. Check if it has a MachineFunction associated with
    // it.
    MachineFunction *MF = MMI.getMachineFunction(F);

    // If it doesn't, then there's nothing to outline from. Move to the next
    // Function.
    if (!MF)
      continue;

    const TargetInstrInfo *TII = MF->getSubtarget().getInstrInfo();

    if (!RunOnAllFunctions && !TII->shouldOutlineFromFunctionByDefault(*MF))
      continue;

    // We have a MachineFunction. Ask the target if it's suitable for outlining.
    // If it isn't, then move on to the next Function in the module.
    if (!TII->isFunctionSafeToOutlineFrom(*MF, OutlineFromLinkOnceODRs))
      continue;

    std::function<unsigned(MachineBasicBlock &)> getFlags =
      [&] (MachineBasicBlock &MBB) {
      return TII->getMachineOutlinerMBBFlags(MBB);
    };

    std::function<InstrType(MachineBasicBlock::iterator &, unsigned)> getInstrType =
      [&] (MachineBasicBlock::iterator &It, unsigned Flags) {
      return TII->getOutliningType(It, Flags);
    };

    // We have a function suitable for outlining. Iterate over every
    // MachineBasicBlock in MF and try to map its instructions to a list of
    // unsigned integers.
    for (MachineBasicBlock &MBB : *MF) {
      // If there isn't anything in MBB, then there's no point in outlining from
      // it.
      if (MBB.empty())
        continue;

      // Check if MBB could be the target of an indirect branch. If it is, then
      // we don't want to outline from it.
      if (MBB.hasAddressTaken())
        continue;

      // MBB is suitable for outlining. Map it to a list of unsigneds.
      // Mapper.convertToUnsignedVec(MBB, *TII);
      Mapper.convertToUnsignedVec(MBB, getFlags, getInstrType);
    }
  }

  // Construct a suffix tree, use it to find candidates, and then outline them.
  SuffixTree ST(Mapper.UnsignedVec);
  std::vector<std::shared_ptr<Candidate>> CandidateList;
  std::vector<OutlinedFunction> FunctionList;

  // Find all of the outlining candidates.
  unsigned MaxCandidateLen =
      buildCandidateList(CandidateList, FunctionList, ST, Mapper);

  // Remove candidates that overlap with other candidates.
  pruneOverlaps(CandidateList, FunctionList, Mapper, MaxCandidateLen);

  // Outline each of the candidates and return true if something was outlined.
  bool OutlinedSomething = outline(M, CandidateList, FunctionList, Mapper);

  return OutlinedSomething;
}
