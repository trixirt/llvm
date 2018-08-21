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


  struct OutlinedFunction : public OutlinedFunctionT<Candidate, MachineFunction> {
      OutlinedFunction(std::vector<Candidate> &Cands,
		       unsigned SequenceSize, unsigned FrameOverhead,
		       unsigned FrameConstructionID)
	: OutlinedFunctionT(Cands, SequenceSize, FrameOverhead,FrameConstructionID) {
      }
    OutlinedFunction() {}
  };
} // namespace outliner
} // namespace llvm

#endif
