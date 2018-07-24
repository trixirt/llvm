//===-- CodeSizeOutliner.h - DCE unreachable internal functions ------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This transform outlines congruent chains of instructions from the current
//   module.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_TRANSFORMS_IPO_CODESIZEOUTLINER_H
#define LLVM_TRANSFORMS_IPO_CODESIZEOUTLINER_H

#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"

namespace llvm {
/// Pass to remove unused function declarations.
class CodeSizeOutlinerPass : public PassInfoMixin<CodeSizeOutlinerPass> {
public:
  PreservedAnalyses run(Module &M, ModuleAnalysisManager &);
};

} // namespace llvm

#endif // LLVM_TRANSFORMS_IPO_CODESIZEOUTLINER_H
