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

  /// The information necessary to create an outlined function for some
/// class of candidate.
  template <typename CANDIDATE, typename FUNCTION>
struct OutlinedFunctionT {

private:
  /// The number of candidates for this \p OutlinedFunction.
  unsigned OccurrenceCount = 0;

public:
  std::vector<std::shared_ptr<CANDIDATE>> Candidates;

  /// The actual outlined function created.
  /// This is initialized after we go through and create the actual function.
  FUNCTION *MF = nullptr;

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
    for (std::shared_ptr<CANDIDATE> &C : Candidates)
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

  OutlinedFunctionT(std::vector<CANDIDATE> &Cands,
                   unsigned SequenceSize, unsigned FrameOverhead,
                   unsigned FrameConstructionID)
      : SequenceSize(SequenceSize), FrameOverhead(FrameOverhead),
        FrameConstructionID(FrameConstructionID) {
    OccurrenceCount = Cands.size();
    for (CANDIDATE &C : Cands)
      Candidates.push_back(std::make_shared<CANDIDATE>(C));

    unsigned B = getBenefit();
    for (std::shared_ptr<CANDIDATE> &C : Candidates)
      C->Benefit = B;
  }

  OutlinedFunctionT() {}
};

} // namespace outliner
} // namespace llvm

#endif
