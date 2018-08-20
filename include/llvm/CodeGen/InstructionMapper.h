//===-- InstructionMapper.h -----------------------------------------*- C++
//-*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CODEGEN_INSTRUCTIONMAPPER_H
#define LLVM_CODEGEN_INSTRUCTIONMAPPER_H

#include "llvm/ADT/DenseMap.h"
#include "llvm/CodeGen/TargetInstrInfo.h"
#include <functional>

namespace llvm {
namespace outliner {

/// Maps \p MachineInstrs to unsigned integers and stores the mappings.
template <typename BLOCK, typename INSTR, typename TRAIT>
struct InstructionMapper {

  /// The next available integer to assign to a \p INSTR that
  /// cannot be outlined.
  ///
  /// Set to -3 for compatability with \p DenseMapInfo<unsigned>.
  unsigned IllegalInstrNumber = -3;

  /// The next available integer to assign to a \p INSTR that can
  /// be outlined.
  unsigned LegalInstrNumber = 0;

  // using InstructionIntegerMapType = DenseMap<INSTR *, unsigned,
  // MachineInstrExpressionTrait>;
  using InstructionIntegerMapType = DenseMap<INSTR *, unsigned, TRAIT>;

  /// Correspondence from \p INSTRs to unsigned integers.
  // DenseMap<INSTR *, unsigned, MachineInstrExpressionTrait>
  // DenseMap<INSTR *, unsigned, InstrExpressionTrait<INSTR>>
  InstructionIntegerMapType InstructionIntegerMap;

  /// Corresponcence from unsigned integers to \p INSTRs.
  /// Inverse of \p InstructionIntegerMap.
  DenseMap<unsigned, INSTR *> IntegerInstructionMap;

  /// The vector of unsigned integers that the module is mapped to.
  std::vector<unsigned> UnsignedVec;

  /// Stores the location of the instruction associated with the integer
  /// at index i in \p UnsignedVec for each index i.
  std::vector<typename BLOCK::iterator> InstrList;

  /// Maps \p *It to a legal integer.
  ///
  /// Updates \p InstrList, \p UnsignedVec, \p InstructionIntegerMap,
  /// \p IntegerInstructionMap, and \p LegalInstrNumber.
  ///
  /// \returns The integer that \p *It was mapped to.
  unsigned mapToLegalUnsigned(typename BLOCK::iterator &It) {

    // Get the integer for this instruction or give it the current
    // LegalInstrNumber.
    InstrList.push_back(It);
    INSTR &MI = *It;
    bool WasInserted;
    // DenseMap<MachineInstr *, unsigned, MachineInstrExpressionTrait>::iterator
    typename InstructionIntegerMapType::iterator ResultIt;
    // using exprTrait = MachineInstrExpressionTrait;
    // using exprTrait = InstrExpressionTrait<INSTR>;
    // using key = MachineInstr *;
    // template<typename T> using key = typename T *;
    // DenseMap<key<typename INSTR>, unsigned, exprTrait>::iterator
    //    ResultIt;
    std::tie(ResultIt, WasInserted) =
        InstructionIntegerMap.insert(std::make_pair(&MI, LegalInstrNumber));
    unsigned MINumber = ResultIt->second;

    // There was an insertion.
    if (WasInserted) {
      LegalInstrNumber++;
      IntegerInstructionMap.insert(std::make_pair(MINumber, &MI));
    }

    UnsignedVec.push_back(MINumber);

    // Make sure we don't overflow or use any integers reserved by the DenseMap.
    if (LegalInstrNumber >= IllegalInstrNumber)
      report_fatal_error("Instruction mapping overflow!");

    assert(LegalInstrNumber != DenseMapInfo<unsigned>::getEmptyKey() &&
           "Tried to assign DenseMap tombstone or empty key to instruction.");
    assert(LegalInstrNumber != DenseMapInfo<unsigned>::getTombstoneKey() &&
           "Tried to assign DenseMap tombstone or empty key to instruction.");

    return MINumber;
  }

  /// Maps \p *It to an illegal integer.
  ///
  /// Updates \p InstrList, \p UnsignedVec, and \p IllegalInstrNumber.
  ///
  /// \returns The integer that \p *It was mapped to.
  unsigned mapToIllegalUnsigned(typename BLOCK::iterator &It) {
    unsigned MINumber = IllegalInstrNumber;

    InstrList.push_back(It);
    UnsignedVec.push_back(IllegalInstrNumber);
    IllegalInstrNumber--;

    assert(LegalInstrNumber < IllegalInstrNumber &&
           "Instruction mapping overflow!");

    assert(IllegalInstrNumber != DenseMapInfo<unsigned>::getEmptyKey() &&
           "IllegalInstrNumber cannot be DenseMap tombstone or empty key!");

    assert(IllegalInstrNumber != DenseMapInfo<unsigned>::getTombstoneKey() &&
           "IllegalInstrNumber cannot be DenseMap tombstone or empty key!");

    return MINumber;
  }

  /// Transforms a \p BLOCK into a \p vector of \p unsigneds
  /// and appends it to \p UnsignedVec and \p InstrList.
  ///
  /// Two instructions are assigned the same integer if they are identical.
  /// If an instruction is deemed unsafe to outline, then it will be assigned an
  /// unique integer. The resulting mapping is placed into a suffix tree and
  /// queried for candidates.
  ///
  /// \param MBB The \p BLOCK to be translated into integers.
  /// \param TII \p TargetInstrInfo for the function.
  void convertToUnsignedVec(
      BLOCK &MBB, std::function<unsigned(BLOCK &)> getFlags,
      std::function<InstrType(typename BLOCK::iterator &, unsigned)>
          getInstrType) {
    // unsigned Flags = TII.getMachineOutlinerMBBFlags(MBB);
    unsigned Flags = getFlags(MBB);

    for (auto It = MBB.begin(), Et = MBB.end(); It != Et; It++) {

      // Keep track of where this instruction is in the module.
      switch (getInstrType(It, Flags)) {
      case InstrType::Illegal:
        mapToIllegalUnsigned(It);
        break;

      case InstrType::Legal:
        mapToLegalUnsigned(It);
        break;

      case InstrType::LegalTerminator:
        mapToLegalUnsigned(It);
        InstrList.push_back(It);
        UnsignedVec.push_back(IllegalInstrNumber);
        IllegalInstrNumber--;
        break;

      case InstrType::Invisible:
        break;
      }
    }

    // After we're done every insertion, uniquely terminate this part of the
    // "string". This makes sure we won't match across basic block or function
    // boundaries since the "end" is encoded uniquely and thus appears in no
    // repeated substring.
    InstrList.push_back(MBB.end());
    UnsignedVec.push_back(IllegalInstrNumber);
    IllegalInstrNumber--;
  }

  InstructionMapper() {
    // Make sure that the implementation of DenseMapInfo<unsigned> hasn't
    // changed.
    assert(DenseMapInfo<unsigned>::getEmptyKey() == (unsigned)-1 &&
           "DenseMapInfo<unsigned>'s empty key isn't -1!");
    assert(DenseMapInfo<unsigned>::getTombstoneKey() == (unsigned)-2 &&
           "DenseMapInfo<unsigned>'s tombstone key isn't -2!");
  }
};

} // namespace outliner
} // namespace llvm

#endif
