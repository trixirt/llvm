//===---- MachineOutliner.h - Outliner data structures ------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
///
/// \file
/// Contains all data structures shared between the outliner implemented in
/// MachineOutliner.cpp and target implementations of the outliner.
///
//===----------------------------------------------------------------------===//

#ifndef LLVM_MACHINEOUTLINER_H
#define LLVM_MACHINEOUTLINER_H

#include "llvm/CodeGen/CandidateT.h"
#include "llvm/CodeGen/LiveRegUnits.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/TargetRegisterInfo.h"
#include "llvm/CodeGen/LivePhysRegs.h"

namespace llvm {
namespace outliner {

  struct Candidate : public CandidateT<MachineBasicBlock> {
  public:
  /// Contains physical register liveness information for the MBB containing
  /// this \p Candidate.
  ///
  /// This is optionally used by the target to calculate more fine-grained
  /// cost model information.
  LiveRegUnits LRU;

  /// Contains the accumulated register liveness information for the
  /// instructions in this \p Candidate.
  ///
  /// This is optionally used by the target to determine which registers have
  /// been used across the sequence.
  LiveRegUnits UsedInSequence;

  Candidate(unsigned StartIdx, unsigned Len,
            MachineBasicBlock::iterator &FirstInst,
            MachineBasicBlock::iterator &LastInst, MachineBasicBlock *MBB,
            unsigned FunctionIdx)
    : CandidateT<MachineBasicBlock>(StartIdx, Len, FirstInst, LastInst, MBB, FunctionIdx) {}
  Candidate() {}

    MachineFunction *getMF() const {
      return getB()->getParent();
    }

  /// Compute the registers that are live across this Candidate.
  /// Used by targets that need this information for cost model calculation.
  /// If a target does not need this information, then this should not be
  /// called.
  void initLRU(const TargetRegisterInfo &TRI) {
    auto BaseMBB = getB();
    
    assert(BaseMBB->getParent()->getRegInfo().tracksLiveness() &&
           "Candidate's Machine Function must track liveness");
    LRU.init(TRI);
    LRU.addLiveOuts(*BaseMBB);

    // Compute liveness from the end of the block up to the beginning of the
    // outlining candidate.
    std::for_each(BaseMBB->rbegin(), (MachineBasicBlock::reverse_iterator)front(),
                  [this](MachineInstr &MI) { LRU.stepBackward(MI); });

    // Walk over the sequence itself and figure out which registers were used
    // in the sequence.
    UsedInSequence.init(TRI);
    std::for_each(front(), std::next(back()),
                  [this](MachineInstr &MI) { UsedInSequence.accumulate(MI); });
  }
};

/// The information necessary to create an outlined function for some
/// class of candidate.
struct OutlinedFunction {

private:
  /// The number of candidates for this \p OutlinedFunction.
  unsigned OccurrenceCount = 0;

public:
  std::vector<std::shared_ptr<Candidate>> Candidates;

  /// The actual outlined function created.
  /// This is initialized after we go through and create the actual function.
  MachineFunction *MF = nullptr;

  /// A number assigned to this function which appears at the end of its name.
  unsigned Name;

  /// The sequence of integers corresponding to the instructions in this
  /// function.
  std::vector<unsigned> Sequence;

  /// Represents the size of a sequence in bytes. (Some instructions vary
  /// widely in size, so just counting the instructions isn't very useful.)
  unsigned SequenceSize;

  /// Target-defined overhead of constructing a frame for this function.
  unsigned FrameOverhead;

  /// Target-defined identifier for constructing a frame for this function.
  unsigned FrameConstructionID;

  /// Return the number of candidates for this \p OutlinedFunction.
  unsigned getOccurrenceCount() { return OccurrenceCount; }

  /// Decrement the occurrence count of this OutlinedFunction and return the
  /// new count.
  unsigned decrement() {
    assert(OccurrenceCount > 0 && "Can't decrement an empty function!");
    OccurrenceCount--;
    return getOccurrenceCount();
  }

  /// Return the number of bytes it would take to outline this
  /// function.
  unsigned getOutliningCost() {
    unsigned CallOverhead = 0;
    for (std::shared_ptr<Candidate> &C : Candidates)
      CallOverhead += C->getCallOverhead();
    return CallOverhead + SequenceSize + FrameOverhead;
  }

  /// Return the size in bytes of the unoutlined sequences.
  unsigned getNotOutlinedCost() { return OccurrenceCount * SequenceSize; }

  /// Return the number of instructions that would be saved by outlining
  /// this function.
  unsigned getBenefit() {
    unsigned NotOutlinedCost = getNotOutlinedCost();
    unsigned OutlinedCost = getOutliningCost();
    return (NotOutlinedCost < OutlinedCost) ? 0
                                            : NotOutlinedCost - OutlinedCost;
  }

  OutlinedFunction(std::vector<Candidate> &Cands,
                   unsigned SequenceSize, unsigned FrameOverhead,
                   unsigned FrameConstructionID)
      : SequenceSize(SequenceSize), FrameOverhead(FrameOverhead),
        FrameConstructionID(FrameConstructionID) {
    OccurrenceCount = Cands.size();
    for (Candidate &C : Cands)
      Candidates.push_back(std::make_shared<outliner::Candidate>(C));

    unsigned B = getBenefit();
    for (std::shared_ptr<Candidate> &C : Candidates)
      C->Benefit = B;
  }

  OutlinedFunction() {}
};
} // namespace outliner
} // namespace llvm

#endif
