#include "llvm/CodeGen/InstructionMapper.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"
#include "llvm/Transforms/IPO.h"

using namespace llvm;
using namespace llvm::outliner;

#define DEBUG_TYPE "iroutliner"

/// Copied for MachineInstrExpressTrait
struct InstructionExpressionTrait : DenseMapInfo<Instruction*> {
  static inline Instruction *getEmptyKey() {
    return nullptr;
  }

  static inline Instruction *getTombstoneKey() {
    return reinterpret_cast<Instruction*>(-1);
  }

  static unsigned getHashValue(const Instruction* const &MI) {
    return 0;
  }

  static bool isEqual(const Instruction* const &LHS,
                      const Instruction* const &RHS) {
    if (RHS == getEmptyKey() || RHS == getTombstoneKey() ||
        LHS == getEmptyKey() || LHS == getTombstoneKey())
      return LHS == RHS;
    return LHS->isIdenticalTo(RHS);
  }
};

struct IROutliner : public ModulePass {
  static char ID;

  using InstructionMapperType =
    InstructionMapper<BasicBlock, Instruction, InstructionExpressionTrait>;

  IROutliner() : ModulePass(ID) {
    initializeIROutlinerPass(*PassRegistry::getPassRegistry());
  }

  /// Construct a suffix tree on the instructions in \p M and outline repeated
  /// strings from that tree.
  bool runOnModule(Module &M) override {

    // Check if there's anything in the module. If it's empty, then there's
    // nothing to outline.
    if (M.empty())
      return false;

    LLVM_DEBUG(dbgs() << "IR Outliner: Running \n");

    InstructionMapperType Mapper;

    // Build instruction mappings for each function in the module. Start by
    // iterating over each Function in M.
    for (Function &F : M) {

      if (F.empty())
	continue;

      // A noop
      std::function<unsigned(BasicBlock &)> getFlags =
	[&] (BasicBlock &BB) {
	return 0;
      };

      std::function<InstrType(BasicBlock::iterator &, unsigned)> getInstrType =
	[&] (BasicBlock::iterator &It, unsigned Flags) {
	// stub
	return InstrType::Legal;
      };


      for (BasicBlock &BB : F) {

	//Mapper.convertToUnsignedVec(BB, getFlags, getInstrType);
      }
    }

#if 0  

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
#endif
    return false;
  }

};

char IROutliner::ID = 0;

namespace llvm {
ModulePass *createIROutlinerPass() {
  return new IROutliner();
}
} // namespace llvm

INITIALIZE_PASS_BEGIN(IROutliner, DEBUG_TYPE,
                      "IR Outliner", false, false)
INITIALIZE_PASS_END(IROutliner, DEBUG_TYPE,
                    "IR Outliner", false, false)



