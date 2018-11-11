//===- Outliner.h - A generic outlining utility interface -------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file includes utilities for defining outliner functionality.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_TRANSFORMS_UTILS_OUTLINER_H
#define LLVM_TRANSFORMS_UTILS_OUTLINER_H

#include "llvm/ADT/ArrayRef.h"
#include "llvm/IR/Instruction.h"
#include <vector>

namespace llvm {
class BitVector;
class BlockFrequencyInfo;
class ProfileSummaryInfo;

/// A potential candidate to be outlined.
struct Candidate {
  /// A unique ID for this outline candidate.
  unsigned ID;

  /// The amount of instructions being saved.
  unsigned Len;

  /// The computed benefit of outlining this candidate.
  unsigned Benefit = 0;

  /// The estimated benefit we receive per occurrence.
  unsigned BenefitPerOccur = 0;

  /// Instruction size of the next candidate.
  unsigned SharedSizeWithNext = 0;

  /// Identifier for each occurrence.
  std::vector<unsigned> Occurrences;

  // Accessors.
  using iterator = std::vector<unsigned>::iterator;
  using const_iterator = std::vector<unsigned>::const_iterator;
  iterator begin() { return Occurrences.begin(); }
  iterator end() { return Occurrences.end(); }
  const_iterator begin() const { return Occurrences.begin(); }
  const_iterator end() const { return Occurrences.end(); }
  size_t size() const { return Occurrences.size(); }

  // Check to see if this chain is still profitable to outline.
  bool isValid() const { return Benefit != 0; }
  // Set this candidate as not profitable.
  void invalidate() { Benefit = 0; }
  // Get the candidate at index Idx.
  unsigned getOccurrence(size_t Idx) const {
    assert(Idx < size() && "Invalid occurrence index.");
    return Occurrences[Idx];
  }
  // Remove the occurrence at index Idx
  void removeOccurrence(size_t Idx) {
    Occurrences[Idx] = Occurrences.back();
    Occurrences.pop_back();
  }

  Candidate(unsigned ID, unsigned Len,
	    std::vector<unsigned> &Occurrences)
      : ID(ID), Len(Len), Occurrences(Occurrences) {}
  Candidate(unsigned ID, unsigned Len) : ID(ID), Len(Len) {}
};

bool findSequentialCandidates(
    function_ref<bool(ArrayRef<unsigned>, unsigned)> PrePruneFn,
    std::vector<unsigned> &Vec, unsigned MinInstructionLen,
    unsigned MinOccurrences, std::vector<Candidate> &CL);

bool pruneSequentialCandidateList(MutableArrayRef<Candidate> CL,
                                  unsigned NumMappedInstructions);

/// Helper struct containing mapping information for a module.
class OutlinerMapper {
public:
  // Get the instruction at index Idx.
  template <typename InstrTy> InstrTy *getInstr(unsigned Idx) {
    return (InstrTy *)InstrVec[Idx];
  }

  // Map a new instruction.
  void mapInstr(Instruction *I) {
    if (I)
      InstructionToIdxMap.try_emplace(I, InstrVec.size());
    InstrVec.push_back(I);
  }

  // Get the index of I inside of the internal vector.
  unsigned getInstrIdx(Instruction *I) {
    auto It = InstructionToIdxMap.find(I);
    return LLVM_UNLIKELY(It == InstructionToIdxMap.end()) ? -1 : It->second;
  }

  // Get the number of mapped instructions.
  unsigned getNumMappedInstructions() const { return InstrVec.size(); }

private:
  /// Stores location of instructions mapped to the corresponding index in
  /// the CCVec.
  std::vector<Instruction *> InstrVec;

  /// Map<Instruction, Index in InstrVec>
  DenseMap<Instruction *, unsigned> InstructionToIdxMap;
};

// Map the module M to prepare for outlining.
std::vector<unsigned>
mapIRModule(OutlinerMapper &OM, Module &M, ProfileSummaryInfo *PSI,
            function_ref<BlockFrequencyInfo &(Function &)> GetBFI);

} // namespace llvm

#endif // LLVM_TRANSFORMS_UTILS_OUTLINER_H
