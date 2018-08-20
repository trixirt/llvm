//===-- InstrType.h -----------------------------------------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CODEGEN_INSTRTYPE_H
#define LLVM_CODEGEN_INSTRTYPE_H

namespace llvm {
namespace outliner {

/// Represents how an instruction should be mapped by the outliner.
/// \p Legal instructions are those which are safe to outline.
/// \p LegalTerminator instructions are safe to outline, but only as the
/// last instruction in a sequence.
/// \p Illegal instructions are those which cannot be outlined.
/// \p Invisible instructions are instructions which can be outlined, but
/// shouldn't actually impact the outlining result.
enum InstrType { Legal, LegalTerminator, Illegal, Invisible };

} // namespace outliner
} // namespace llvm

#endif
