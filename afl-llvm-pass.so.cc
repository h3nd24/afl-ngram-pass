/*
  Copyright 2015 Google LLC All rights reserved.

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at:

    http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
*/

/*
   american fuzzy lop - LLVM-mode instrumentation pass
   ---------------------------------------------------

   Written by Laszlo Szekeres <lszekeres@google.com> and
              Michal Zalewski <lcamtuf@google.com>

   LLVM integration design comes from Laszlo Szekeres. C bits copied-and-pasted
   from afl-as.c are Michal's fault.

   This library is plugged into LLVM when invoking clang through afl-clang-fast.
   It tells the compiler to add code roughly equivalent to the bits discussed
   in ../afl-as.h.
*/

#define AFL_LLVM_PASS

#include "../config.h"
#include "../debug.h"
#include "llvm-config.h"

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/MathExtras.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

using namespace llvm;

namespace {

class AFLCoverage : public ModulePass {

public:
  static char ID;
  AFLCoverage() : ModulePass(ID) {}

  bool runOnModule(Module &M) override;

  // StringRef getPassName() const override {
  //  return "American Fuzzy Lop Instrumentation";
  // }
};

} // namespace

char AFLCoverage::ID = 0;

bool AFLCoverage::runOnModule(Module &M) {

  LLVMContext &C = M.getContext();

  IntegerType *Int8Ty = IntegerType::getInt8Ty(C);
  IntegerType *Int32Ty = IntegerType::getInt32Ty(C);

  /* Show a banner */

  char be_quiet = 0;

  if (isatty(2) && !getenv("AFL_QUIET")) {

    SAYF(cCYA "afl-llvm-pass " cBRI VERSION cRST
              " by <lszekeres@google.com, adrian.herrera@anu.edu.au, hendra.gunadi@anu.edu.au>\n");

  } else
    be_quiet = 1;

  /* Decide instrumentation ratio */

  char *inst_ratio_str = getenv("AFL_INST_RATIO");
  unsigned int inst_ratio = 100;

  if (inst_ratio_str) {

    if (sscanf(inst_ratio_str, "%u", &inst_ratio) != 1 || !inst_ratio ||
        inst_ratio > 100)
      FATAL("Bad value of AFL_INST_RATIO (must be between 1 and 100)");
  }

  /* Get globals for the SHM region and the previous location. Note that
     __afl_prev_loc is thread-local. */

  GlobalVariable *AFLMapPtr =
      new GlobalVariable(M, PointerType::get(Int8Ty, 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_area_ptr");

  /* Decide previous location vector size (must be a power of two) */

  char *ngram_size_str = getenv("AFL_NGRAM_SIZE");
  unsigned int ngram_size = 4;

  if (ngram_size_str) {
    if (sscanf(ngram_size_str, "%u", &ngram_size) != 1 || ngram_size < 2 ||
        ngram_size > MAX_NGRAM_SIZE) {
      FATAL(
          "Bad value of AFL_NGRAM_SIZE (must be between 2 and MAX_NGRAM_SIZE)");
    }
  }

  unsigned HistSize = ngram_size - 1;

  GlobalVariable *AFLHist = new GlobalVariable(
      M, PointerType::get(Int32Ty, 0), /* isConstant */ false, GlobalValue::ExternalLinkage,
      /* Initializer */ nullptr, "__afl_hist",
      /* InsertBefore */ nullptr, GlobalVariable::GeneralDynamicTLSModel,
      /* AddressSpace */ 0, /* IsExternallyInitialized */ false);

  GlobalVariable *AFLInsertLoc = new GlobalVariable(
      M, Int32Ty, /* isConstant */ false, GlobalValue::ExternalLinkage,
      /* Initializer */ nullptr, "__afl_insert_location",
      /* InsertBefore */ nullptr, GlobalVariable::GeneralDynamicTLSModel,
      /* AddressSpace */ 0, /* IsExternallyInitialized */ false);

  GlobalVariable *AFLAcc = new GlobalVariable(
      M, Int32Ty, /* isConstant */ false, GlobalValue::ExternalLinkage,
      /* Initializer */ nullptr, "__afl_acc",
      /* InsertBefore */ nullptr, GlobalVariable::GeneralDynamicTLSModel,
      /* AddressSpace */ 0, /* IsExternallyInitialized */ false);

  GlobalVariable *AFLPrevLoc = new GlobalVariable(
      M, Int32Ty, /* isConstant */ false, GlobalValue::ExternalLinkage,
      /* Initializer */ nullptr, "__afl_prev_loc",
      /* InsertBefore */ nullptr, GlobalVariable::GeneralDynamicTLSModel,
      /* AddressSpace */ 0, /* IsExternallyInitialized */ false);

  /* Instrument all the things! */

  int inst_blocks = 0;

  for (auto &F : M)
    for (auto &BB : F) {

      BasicBlock::iterator IP = BB.getFirstInsertionPt();
      IRBuilder<> IRB(&(*IP));

      if (AFL_R(100) >= inst_ratio)
        continue;

      /* Make up cur_loc */

      unsigned int cur_loc = AFL_R(MAP_SIZE);

      ConstantInt *CurLoc = ConstantInt::get(Int32Ty, cur_loc);

      /* Load SHM pointer */

      LoadInst *Acc = IRB.CreateLoad(AFLAcc); /* load the accumulator */
      LoadInst *PrevLoc = IRB.CreateLoad(AFLPrevLoc); /* load the previous block */
      Acc->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value* CurEdge = IRB.CreateXor(CurLoc, PrevLoc); /* current edge: (prev_loc >> 1) ^ cur_loc = block_trans */
      LoadInst *MapPtr = IRB.CreateLoad(AFLMapPtr); /* load the reference to the bitmap */
      MapPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      /* hash to the bitmap, calculated as (prev_block_trans >> 1) ^ block_trans,
         where prev_block_trans = (block_trans_1 ^ block_trans_2 ^ ... ^ block_trans_{n-1}).
         As we already right shift the entry, we do not right shift Acc anymore, i.e.,
         Acc = (prev_block_trans >> 1)  */
      Value *MapPtrIdx = IRB.CreateGEP(
          MapPtr, IRB.CreateZExt(IRB.CreateXor(Acc, CurEdge), Int32Ty));

      /* Update bitmap */

      LoadInst *Counter = IRB.CreateLoad(MapPtrIdx);
      Counter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *Incr = IRB.CreateAdd(Counter, ConstantInt::get(Int8Ty, 1));
      IRB.CreateStore(Incr, MapPtrIdx)
          ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      /* Load the circular queue at the current index */
      LoadInst *Hist = IRB.CreateLoad(AFLHist);
      Hist->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      LoadInst *InsertLoc = IRB.CreateLoad(AFLInsertLoc);
      InsertLoc->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *HistIdx = IRB.CreateGEP(Hist, InsertLoc); 

      Value *RightShiftedCurEdge = IRB.CreateLShr(CurEdge, (uint64_t)1); /* Right shift the current edge */

      /* Update the acummulator: Get OldestEdge, which is the oldest value to be removed from Acc.
         Acc = Acc ^ CurEdge ^ OldestEdge. We don't even need flag, when the pointer wrap around then the array will have non-zero value. */
      LoadInst *OldestEdge = IRB.CreateLoad(HistIdx);
      Value *NewAcc = IRB.CreateXor(IRB.CreateXor(Acc, RightShiftedCurEdge), OldestEdge);
      IRB.CreateStore(NewAcc, AFLAcc) /* Store the new accumulator */
          ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      /* Insert the latest location right-shifted by one to the Hist.
         Note that currently we right-shift the entry as opposed to right-shift the acummulator before the index calculation.
         Arguably they achieve the same effect and should have the same overhead. */
      IRB.CreateStore(RightShiftedCurEdge, HistIdx)
          ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      /* Get the new insertion point, which is addition modulo PrevLocSize operation */ 
      IRB.CreateStore(IRB.CreateURem(IRB.CreateAdd(InsertLoc, ConstantInt::get(Int32Ty, 1)), 
          ConstantInt::get(Int32Ty, HistSize)), AFLInsertLoc)
          ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      /* Store the PrevLoc */
      IRB.CreateStore(IRB.CreateLShr(CurLoc, (uint64_t) 1), AFLPrevLoc)
          ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      inst_blocks++;
    }

  /* Say something nice. */

  if (!be_quiet) {

    if (!inst_blocks)
      WARNF("No instrumentation targets found.");
    else
      OKF("Instrumented %u locations (%s mode, ratio %u%%).", inst_blocks,
          getenv("AFL_HARDEN")
              ? "hardened"
              : ((getenv("AFL_USE_ASAN") || getenv("AFL_USE_MSAN"))
                     ? "ASAN/MSAN"
                     : "non-hardened"),
          inst_ratio);
  }

  return true;
}

static void registerAFLPass(const PassManagerBuilder &,
                            legacy::PassManagerBase &PM) {

  PM.add(new AFLCoverage());
}

static RegisterStandardPasses
    RegisterAFLPass(PassManagerBuilder::EP_ModuleOptimizerEarly,
                    registerAFLPass);

static RegisterStandardPasses
    RegisterAFLPass0(PassManagerBuilder::EP_EnabledOnOptLevel0,
                     registerAFLPass);
