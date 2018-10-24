//===-- IROutliner.h - Base class for the IRO pass ------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Generates functions by collecting a module's common IR sequences.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_TRANSFORMS_IPO_IROUTLINER_H
#define LLVM_TRANSFORMS_IPO_IROUTLINER_H

#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"

namespace llvm {
class IROutlinerPass : public PassInfoMixin<IROutlinerPass> {
public:
  PreservedAnalyses run(Module &M, ModuleAnalysisManager &);
};

} // namespace llvm

#endif // LLVM_TRANSFORMS_IPO_IROUTLINER_H
