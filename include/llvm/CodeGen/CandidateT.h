//===-- CandidataT.h -----------------------------------------*- C++
//-*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CODEGEN_CANDIDATET_H
#define LLVM_CODEGEN_CANDIDATET_H

namespace llvm {
namespace outliner {

/// An individual sequence of instructions to be replaced with a call to
/// an outlined function.
  template <typename BLOCK>  
struct CandidateT {
private:
  /// The start index of this \p Candidate in the instruction list.
  unsigned StartIdx;

  /// The number of instructions in this \p Candidate.
  unsigned Len;

  // The first instruction in this \p Candidate.
  typename BLOCK::iterator FirstInst;

  // The last instruction in this \p Candidate.
  typename BLOCK::iterator LastInst;

  // The basic block that contains this Candidate.
  BLOCK *B;

  /// Cost of calling an outlined function from this point as defined by the
  /// target.
  unsigned CallOverhead;

public:
  /// The index of this \p Candidate's \p OutlinedFunction in the list of
  /// \p OutlinedFunctions.
  unsigned FunctionIdx;

  /// Set to false if the candidate overlapped with another candidate.
  bool InCandidateList = true;

  /// Identifier denoting the instructions to emit to call an outlined function
  /// from this point. Defined by the target.
  unsigned CallConstructionID;

  /// Return the number of instructions in this Candidate.
  unsigned getLength() const { return Len; }

  /// Return the start index of this candidate.
  unsigned getStartIdx() const { return StartIdx; }

  /// Return the end index of this candidate.
  unsigned getEndIdx() const { return StartIdx + Len - 1; }

  /// Set the CallConstructionID and CallOverhead of this candidate to CID and
  /// CO respectively.
  void setCallInfo(unsigned CID, unsigned CO) {
    CallConstructionID = CID;
    CallOverhead = CO;
  }

  /// Returns the call overhead of this candidate if it is in the list.
  unsigned getCallOverhead() const {
    return InCandidateList ? CallOverhead : 0;
  }

  typename BLOCK::iterator &front() { return FirstInst; }
  typename BLOCK::iterator &back() { return LastInst; }
  BLOCK *getB() const { return B; }

  /// The number of instructions that would be saved by outlining every
  /// candidate of this type.
  ///
  /// This is a fixed value which is not updated during the candidate pruning
  /// process. It is only used for deciding which candidate to keep if two
  /// candidates overlap. The true benefit is stored in the OutlinedFunction
  /// for some given candidate.
  unsigned Benefit = 0;

  CandidateT(unsigned StartIdx, unsigned Len,
            typename BLOCK::iterator &FirstInst,
            typename BLOCK::iterator &LastInst, BLOCK *B,
            unsigned FunctionIdx)
      : StartIdx(StartIdx), Len(Len), FirstInst(FirstInst), LastInst(LastInst),
        B(B), FunctionIdx(FunctionIdx) {}
  CandidateT() {}

  /// Used to ensure that \p Candidates are outlined in an order that
  /// preserves the start and end indices of other \p Candidates.
  bool operator<(const CandidateT &RHS) const {
    return getStartIdx() > RHS.getStartIdx();
  }
};
 
} // namespace outliner
} // namespace llvm

#endif
