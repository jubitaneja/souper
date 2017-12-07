// Copyright 2014 The Souper Authors. All rights reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#define DEBUG_TYPE "souper"

#include "llvm/ADT/APInt.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Instruction.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ErrorHandling.h"
#include "souper/Extractor/Solver.h"
#include "souper/Infer/InstSynthesis.h"
#include "souper/KVStore/KVStore.h"
#include "souper/Parser/Parser.h"

#include <sstream>
#include <unordered_map>

STATISTIC(MemHitsInfer, "Number of internal cache hits for infer()");
STATISTIC(MemMissesInfer, "Number of internal cache misses for infer()");
STATISTIC(MemHitsIsValid, "Number of internal cache hits for isValid()");
STATISTIC(MemMissesIsValid, "Number of internal cache misses for isValid()");
STATISTIC(ExternalHits, "Number of external cache hits");
STATISTIC(ExternalMisses, "Number of external cache misses");

using namespace souper;
using namespace llvm;

namespace {

static cl::opt<bool> NoInfer("souper-no-infer",
    cl::desc("Populate the external cache, but don't infer replacements"),
    cl::init(false));
static cl::opt<bool> InferNop("souper-infer-nop",
    cl::desc("Infer that the output is the same as an input value (default=false)"),
    cl::init(false));
static cl::opt<bool> InferInts("souper-infer-iN",
    cl::desc("Infer iN integers for N>1 (default=true)"),
    cl::init(true));
static cl::opt<bool> InferInsts("souper-infer-inst",
    cl::desc("Infer instructions (default=false)"),
    cl::init(false));
static cl::opt<int> MaxLHSSize("souper-max-lhs-size",
    cl::desc("Max size of LHS (in bytes) to put in external cache"),
    cl::init(1024));

class BaseSolver : public Solver {
  std::unique_ptr<SMTLIBSolver> SMTSolver;
  unsigned Timeout;

  void findVars(Inst *I, std::set<Inst *> &Visited,
                std::vector<Inst *> &Guesses, unsigned Width) {
    if (!Visited.insert(I).second)
      return;
    if (I->K == Inst::Var && I->Width == Width)
      Guesses.emplace_back(I);
    for (auto Op : I->Ops)
      findVars(Op, Visited, Guesses, Width);
  }

public:
  BaseSolver(std::unique_ptr<SMTLIBSolver> SMTSolver, unsigned Timeout)
      : SMTSolver(std::move(SMTSolver)), Timeout(Timeout) {}

  bool testZeroSign(const BlockPCs &BPCs,
                const std::vector<InstMapping> &PCs,
                APInt &Negative, Inst *LHS,
                InstContext &IC) {
    unsigned W = LHS->Width;
    APInt Zero = APInt::getNullValue(W);
    Inst *Mask = IC.getConst(Negative);
    InstMapping Mapping(IC.getInst(Inst::And, W, { LHS, Mask }), IC.getConst(Zero));
    bool IsSat;
    Mapping.LHS->DemandedBits = APInt::getAllOnesValue(Mapping.LHS->Width);
    std::error_code EC = SMTSolver->isSatisfiable(BuildQuery(BPCs, PCs, Mapping, 0),
                                                  IsSat, 0, 0, Timeout);
    if (EC)
      llvm::report_fatal_error("stopping due to error");
    return !IsSat;
  }

  bool testOneSign(const BlockPCs &BPCs,
                const std::vector<InstMapping> &PCs,
                APInt &Negative, Inst *LHS,
                InstContext &IC) {
    unsigned W = LHS->Width;
    Inst *Mask = IC.getConst(Negative);
    InstMapping Mapping(IC.getInst(Inst::And, W, { LHS, Mask }), Mask);
    bool IsSat;
    Mapping.LHS->DemandedBits = APInt::getAllOnesValue(Mapping.LHS->Width);
    std::error_code EC = SMTSolver->isSatisfiable(BuildQuery(BPCs, PCs, Mapping, 0),
                                                  IsSat, 0, 0, Timeout);
    if (EC)
      llvm::report_fatal_error("stopping due to error");
    return !IsSat;
  }

  std::error_code Negative(const BlockPCs &BPCs,
                           const std::vector<InstMapping> &PCs,
                           Inst *LHS, APInt &Negative,
                           InstContext &IC) override {
    unsigned W = LHS->Width;
    Negative = APInt::getNullValue(W);
    APInt NegativeGuess = Negative | APInt::getOneBitSet(W, W-1);
    if (testZeroSign(BPCs, PCs, NegativeGuess, LHS, IC))
      Negative = APInt::getNullValue(W);
    else if (testOneSign(BPCs, PCs, NegativeGuess, LHS, IC))
      Negative = NegativeGuess;
    return std::error_code();
  }

  std::error_code nonNegative(const BlockPCs &BPCs,
                              const std::vector<InstMapping> &PCs,
                              Inst *LHS, APInt &NonNegative,
                              InstContext &IC) override {
    unsigned W = LHS->Width;
    NonNegative = APInt::getNullValue(W);
    APInt NonNegativeGuess = NonNegative | APInt::getOneBitSet(W, W-1);
    if (testZeroSign(BPCs, PCs, NonNegativeGuess, LHS, IC))
      NonNegative = APInt::getNullValue(W);
    else if (testOneSign(BPCs, PCs, NonNegativeGuess, LHS, IC))
      NonNegative = NonNegativeGuess;
    else
      NonNegative = NonNegativeGuess; //if sign-bit is not guessed as 0 or 1, set non-negative signbit to 1, so that nothing is inferred by souper at the end
    return std::error_code();
  }

  bool testKnown(const BlockPCs &BPCs,
                const std::vector<InstMapping> &PCs,
                APInt &Zeros, APInt &Ones, Inst *LHS,
                InstContext &IC) {
    unsigned W = LHS->Width;
    Inst *Mask = IC.getConst(Zeros | Ones);
    InstMapping Mapping(IC.getInst(Inst::And, W, { LHS, Mask }), IC.getConst(Ones));
    bool IsSat;
    Mapping.LHS->DemandedBits = APInt::getAllOnesValue(Mapping.LHS->Width);
    std::error_code EC = SMTSolver->isSatisfiable(BuildQuery(BPCs, PCs, Mapping, 0),
                                                  IsSat, 0, 0, Timeout);
    if (EC)
      llvm::report_fatal_error("stopping due to error");
    return !IsSat;
  }

  std::error_code knownBits(const BlockPCs &BPCs,
                          const std::vector<InstMapping> &PCs,
                          Inst *LHS, APInt &Zeros, APInt &Ones,
                          InstContext &IC) override {
    unsigned W = LHS->Width;
    Ones = APInt::getNullValue(W);
    Zeros = APInt::getNullValue(W);
    for (unsigned I=0; I<W; I++) {
      APInt ZeroGuess = Zeros | APInt::getOneBitSet(W, I);
      if (testKnown(BPCs, PCs, ZeroGuess, Ones, LHS, IC)) {
        Zeros = ZeroGuess;
        continue;
      }
      APInt OneGuess = Ones | APInt::getOneBitSet(W, I);
      if (testKnown(BPCs, PCs, Zeros, OneGuess, LHS, IC))
        Ones = OneGuess;
    }
    return std::error_code();
  }

  std::error_code powerTwo(const BlockPCs &BPCs,
                              const std::vector<InstMapping> &PCs,
                              Inst *LHS, APInt &PowTwo,
                              InstContext &IC) override {
    unsigned W = LHS->Width;
    APInt ConstOne(W, 1, false);
    APInt ZeroGuess(W, 0, false);
    APInt TrueGuess(1, 1, false);
    Inst *PowerMask = IC.getInst(Inst::And, W, {LHS, IC.getInst(Inst::Sub, W, {LHS, IC.getConst(ConstOne)})});
    Inst *Zero = IC.getConst(ZeroGuess);
    Inst *True = IC.getConst(TrueGuess);
    Inst *PowerTwoInst = IC.getInst(Inst::And, 1, {IC.getInst(Inst::Ne, 1, {LHS, Zero}),
                                                   IC.getInst(Inst::Eq, 1, {PowerMask, Zero})});
    InstMapping Mapping(PowerTwoInst, True);
    //InstMapping Mapping(PowerMask, Zero);
    bool IsSat;
    Mapping.LHS->DemandedBits = APInt::getAllOnesValue(Mapping.LHS->Width);
    std::error_code EC = SMTSolver->isSatisfiable(BuildQuery(BPCs, PCs, Mapping, 0),
                                                  IsSat, 0, 0, Timeout);
    if (EC)
      llvm::report_fatal_error("stopping due to error");

    if (!IsSat)
      PowTwo = APInt(1, 1, false);
    else
      PowTwo = APInt(1, 0, false);
    return std::error_code();
  }

  std::error_code nonZero(const BlockPCs &BPCs,
                              const std::vector<InstMapping> &PCs,
                              Inst *LHS, APInt &NonZero,
                              InstContext &IC) override {
    unsigned W = LHS->Width;
    APInt ZeroGuess(W, 0, false);
    APInt TrueGuess(1, 1, false);
    Inst *Zero = IC.getConst(ZeroGuess);
    Inst *True = IC.getConst(TrueGuess);
    Inst *NonZeroGuess = IC.getInst(Inst::Ne, 1, {LHS, Zero});
    InstMapping Mapping(NonZeroGuess, True);
    bool IsSat;
    Mapping.LHS->DemandedBits = APInt::getAllOnesValue(Mapping.LHS->Width);
    std::error_code EC = SMTSolver->isSatisfiable(BuildQuery(BPCs, PCs, Mapping, 0),
                                                  IsSat, 0, 0, Timeout);
    if (EC)
      llvm::report_fatal_error("stopping due to error");

    if (!IsSat)
      NonZero = APInt(1, 1, false);
    else
      NonZero = APInt(1, 0, false);
    return std::error_code();
  }

  std::error_code signBits(const BlockPCs &BPCs,
                              const std::vector<InstMapping> &PCs,
                              Inst *LHS, unsigned &SignBits,
                              InstContext &IC) override {
    unsigned W = LHS->Width;
    SignBits = 1;
    APInt Zero(W, 0, false);
    Inst *AllZeros = IC.getConst(Zero);
    APInt Ones = APInt::getAllOnesValue(W);
    Inst *AllOnes = IC.getConst(Ones);
    APInt TrueGuess(1, 1, false);
    Inst *True = IC.getConst(TrueGuess);
    // guess signbits starting from 2, because 1 is by default
    for (unsigned I=2; I<=W; I++) {
      APInt SA(W, W-I, false);
      Inst *ShiftAmt = IC.getConst(SA);
      Inst *Res = IC.getInst(Inst::AShr, W, {LHS, ShiftAmt}); 
      Inst *Guess1 = IC.getInst(Inst::Eq, 1, {Res, AllZeros});
      Inst *Guess2 = IC.getInst(Inst::Eq, 1, {Res, AllOnes});
      Inst *Guess = IC.getInst(Inst::Or, 1, {Guess1, Guess2}); 
      InstMapping Mapping(Guess, True);
      bool IsSat;
      Mapping.LHS->DemandedBits = APInt::getAllOnesValue(Mapping.LHS->Width);
      std::error_code EC = SMTSolver->isSatisfiable(BuildQuery(BPCs, PCs, Mapping, 0),
                                                    IsSat, 0, 0, Timeout);
      if (EC)
        llvm::report_fatal_error("stopping due to error");
  
      if (!IsSat) { //guess is correct, keep looking for more signbits
        SignBits = I;
        continue;
      } else {
        break;
      }
    }
    return std::error_code();
  }

  std::error_code testDemandedBits(const BlockPCs &BPCs,
                           const std::vector<InstMapping> &PCs,
                           Inst *LHS, APInt &DB,
                           InstContext &IC) override {
    unsigned W = LHS->Width;
    Ones = APInt::getNullValue(W);
    Zeros = APInt::getNullValue(W);
    for (unsigned I=0; I<W; I++) {
      APInt ZeroGuess = Zeros | APInt::getOneBitSet(W, I);
      if (testKnown(BPCs, PCs, ZeroGuess, Ones, LHS, IC)) {
        Zeros = ZeroGuess;
        continue;
      } else {
        APInt OneGuess = Ones | APInt::getOneBitSet(W, I);
        Ones = OneGuess;
    }
    DB = Ones;
    return std::error_code();
  }

  std::error_code infer(const BlockPCs &BPCs,
                        const std::vector<InstMapping> &PCs,
                        Inst *LHS, Inst *&RHS, InstContext &IC) override {
    std::error_code EC;

    /*
     * TODO: try to synthesize undef before synthesizing a concrete
     * integer
     */

    /*
     * Even though we have real integer synthesis below, first try to
     * guess a few constants that are likely to be cheap for the
     * backend to make
     */
    if (InferInts || LHS->Width == 1) {
      std::vector<Inst *>Guesses { IC.getConst(APInt(LHS->Width, 0)),
                                   IC.getConst(APInt(LHS->Width, 1)) };
      if (LHS->Width > 1)
        Guesses.emplace_back(IC.getConst(APInt(LHS->Width, -1)));
      for (auto I : Guesses) {
        InstMapping Mapping(LHS, I);
        std::string Query = BuildQuery(BPCs, PCs, Mapping, 0);
        if (Query.empty())
          return std::make_error_code(std::errc::value_too_large);
        bool IsSat;
        EC = SMTSolver->isSatisfiable(Query, IsSat, 0, 0, Timeout);
        if (EC)
          return EC;
        if (!IsSat) {
          RHS = I;
          return EC;
        }
      }
    }

    if (InferInts && SMTSolver->supportsModels() && LHS->Width > 1) {
      std::vector<Inst *> ModelInsts;
      std::vector<llvm::APInt> ModelVals;
      Inst *I = IC.createVar(LHS->Width, "constant");
      InstMapping Mapping(LHS, I);
      std::string Query = BuildQuery(BPCs, PCs, Mapping, &ModelInsts, /*Negate=*/true);
      if (Query.empty())
        return std::make_error_code(std::errc::value_too_large);
      bool IsSat;
      EC = SMTSolver->isSatisfiable(Query, IsSat, ModelInsts.size(),
                                    &ModelVals, Timeout);
      if (EC)
        return EC;
      if (IsSat) {
        // We found a model for a constant
        Inst *Const = 0;
        for (unsigned J = 0; J != ModelInsts.size(); ++J) {
          if (ModelInsts[J]->Name == "constant") {
            Const = IC.getConst(ModelVals[J]);
            break;
          }
        }
        assert(Const && "there must be a model for the constant");
        // Check if the constant is valid for all inputs
        InstMapping ConstMapping(LHS, Const);
        std::string Query = BuildQuery(BPCs, PCs, ConstMapping, 0);
        if (Query.empty())
          return std::make_error_code(std::errc::value_too_large);
        EC = SMTSolver->isSatisfiable(Query, IsSat, 0, 0, Timeout);
        if (EC)
          return EC;
        if (!IsSat) {
          RHS = Const;
          return EC;
        }
      }
    }

    if (InferNop) {
      std::vector<Inst *> Guesses;
      std::set<Inst *> Visited;
      findVars(LHS, Visited, Guesses, LHS->Width);
      for (auto I : Guesses) {
        if (LHS == I)
          continue;
        InstMapping Mapping(LHS, I);
        std::string Query = BuildQuery(BPCs, PCs, Mapping, 0);
        if (Query.empty())
          return std::make_error_code(std::errc::value_too_large);
        bool IsSat;
        EC = SMTSolver->isSatisfiable(Query, IsSat, 0, 0, Timeout);
        if (EC)
          return EC;
        if (!IsSat) {
          RHS = I;
          return EC;
        }
      }
    }

    if (InferInsts && SMTSolver->supportsModels()) {
      InstSynthesis IS;
      EC = IS.synthesize(SMTSolver.get(), BPCs, PCs, LHS, RHS, IC, Timeout);
      if (EC || RHS)
        return EC;
    }

    RHS = 0;
    return EC;
  }

  std::error_code isValid(const BlockPCs &BPCs,
                          const std::vector<InstMapping> &PCs,
                          InstMapping Mapping, bool &IsValid,
                          std::vector<std::pair<Inst *, llvm::APInt>> *Model)
  override {
    std::string Query;
    if (Model && SMTSolver->supportsModels()) {
      std::vector<Inst *> ModelInsts;
      std::string Query = BuildQuery(BPCs, PCs, Mapping, &ModelInsts);
      if (Query.empty())
        return std::make_error_code(std::errc::value_too_large);
      bool IsSat;
      std::vector<llvm::APInt> ModelVals;
      std::error_code EC = SMTSolver->isSatisfiable(
          Query, IsSat, ModelInsts.size(), &ModelVals, Timeout);
      if (!EC) {
        if (IsSat) {
          for (unsigned I = 0; I != ModelInsts.size(); ++I) {
            Model->push_back(std::make_pair(ModelInsts[I], ModelVals[I]));
          }
        }
        IsValid = !IsSat;
      }
      return EC;
    } else {
      std::string Query = BuildQuery(BPCs, PCs, Mapping, 0);
      if (Query.empty())
        return std::make_error_code(std::errc::value_too_large);
      bool IsSat;
      std::error_code EC = SMTSolver->isSatisfiable(Query, IsSat, 0, 0, Timeout);
      IsValid = !IsSat;
      return EC;
    }
  }

  std::string getName() override {
    return SMTSolver->getName();
  }
};

class MemCachingSolver : public Solver {
  std::unique_ptr<Solver> UnderlyingSolver;
  std::unordered_map<std::string, std::pair<std::error_code, bool>> IsValidCache;
  std::unordered_map<std::string, std::pair<std::error_code, std::string>>
    InferCache;

public:
  MemCachingSolver(std::unique_ptr<Solver> UnderlyingSolver)
      : UnderlyingSolver(std::move(UnderlyingSolver)) {}

  std::error_code infer(const BlockPCs &BPCs,
                        const std::vector<InstMapping> &PCs,
                        Inst *LHS, Inst *&RHS, InstContext &IC) override {
    ReplacementContext Context;
    std::string Repl = GetReplacementLHSString(BPCs, PCs, LHS, Context);
    const auto &ent = InferCache.find(Repl);
    if (ent == InferCache.end()) {
      ++MemMissesInfer;
      std::error_code EC = UnderlyingSolver->infer(BPCs, PCs, LHS, RHS, IC);
      std::string RHSStr;
      if (!EC && RHS) {
        RHSStr = GetReplacementRHSString(RHS, Context);
      }
      InferCache.emplace(Repl, std::make_pair(EC, RHSStr));
      return EC;
    } else {
      ++MemHitsInfer;
      std::string ES;
      StringRef S = ent->second.second;
      if (S == "") {
        RHS = 0;
      } else {
        ParsedReplacement R = ParseReplacementRHS(IC, "<cache>", S, Context, ES);
        if (ES != "")
          return std::make_error_code(std::errc::protocol_error);
        RHS = R.Mapping.RHS;
      }
      return ent->second.first;
    }
  }

  std::error_code isValid(const BlockPCs &BPCs,
                          const std::vector<InstMapping> &PCs,
                          InstMapping Mapping, bool &IsValid,
                          std::vector<std::pair<Inst *, llvm::APInt>> *Model)
    override {
    // TODO: add caching support for models.
    if (Model)
      return UnderlyingSolver->isValid(BPCs, PCs, Mapping, IsValid, Model);

    std::string Repl = GetReplacementString(BPCs, PCs, Mapping);
    const auto &ent = IsValidCache.find(Repl);
    if (ent == IsValidCache.end()) {
      ++MemMissesIsValid;
      std::error_code EC = UnderlyingSolver->isValid(BPCs, PCs,
                                                     Mapping, IsValid, 0);
      IsValidCache.emplace(Repl, std::make_pair(EC, IsValid));
      return EC;
    } else {
      ++MemHitsIsValid;
      IsValid = ent->second.second;
      return ent->second.first;
    }
  }

  std::string getName() override {
    return UnderlyingSolver->getName() + " + internal cache";
  }

  std::error_code nonNegative(const BlockPCs &BPCs,
                              const std::vector<InstMapping> &PCs,
                              Inst *LHS, APInt &NonNegative,
                              InstContext &IC) override {
    return UnderlyingSolver->nonNegative(BPCs, PCs, LHS, NonNegative, IC);
  }

  std::error_code Negative(const BlockPCs &BPCs,
                              const std::vector<InstMapping> &PCs,
                              Inst *LHS, APInt &Negative,
                              InstContext &IC) override {
    return UnderlyingSolver->Negative(BPCs, PCs, LHS, Negative, IC);
  }

  std::error_code knownBits(const BlockPCs &BPCs,
                            const std::vector<InstMapping> &PCs,
                            Inst *LHS, APInt &Zeros, APInt &Ones,
                            InstContext &IC) override {
    return UnderlyingSolver->knownBits(BPCs, PCs, LHS, Zeros, Ones, IC);
  }

  std::error_code powerTwo(const BlockPCs &BPCs,
                            const std::vector<InstMapping> &PCs,
                            Inst *LHS, APInt &PowerTwo,
                            InstContext &IC) override {
    return UnderlyingSolver->powerTwo(BPCs, PCs, LHS, PowerTwo, IC);
  }

  std::error_code testDemandedBits(const BlockPCs &BPCs,
                            const std::vector<InstMapping> &PCs,
                            Inst *LHS, APInt &DB,
                            InstContext &IC) override {
    return UnderlyingSolver->testDemandedBits(BPCs, PCs, LHS, DB, IC);
  }

  std::error_code nonZero(const BlockPCs &BPCs,
                            const std::vector<InstMapping> &PCs,
                            Inst *LHS, APInt &NonZero,
                            InstContext &IC) override {
    return UnderlyingSolver->nonZero(BPCs, PCs, LHS, NonZero, IC);
  }

  std::error_code signBits(const BlockPCs &BPCs,
                            const std::vector<InstMapping> &PCs,
                            Inst *LHS, unsigned &SignBits,
                            InstContext &IC) override {
    return UnderlyingSolver->signBits(BPCs, PCs, LHS, SignBits, IC);
  }

};

class ExternalCachingSolver : public Solver {
  std::unique_ptr<Solver> UnderlyingSolver;
  KVStore *KV;

public:
  ExternalCachingSolver(std::unique_ptr<Solver> UnderlyingSolver, KVStore *KV)
      : UnderlyingSolver(std::move(UnderlyingSolver)), KV(KV) {
  }

  std::error_code infer(const BlockPCs &BPCs,
                        const std::vector<InstMapping> &PCs,
                        Inst *LHS, Inst *&RHS, InstContext &IC) override {
    ReplacementContext Context;
    std::string LHSStr = GetReplacementLHSString(BPCs, PCs, LHS, Context);
    if (LHSStr.length() > MaxLHSSize)
      return std::make_error_code(std::errc::value_too_large);
    std::string S;
    if (KV->hGet(LHSStr, "result", S)) {
      ++ExternalHits;
      if (S == "") {
        RHS = 0;
      } else {
        std::string ES;
        ParsedReplacement R = ParseReplacementRHS(IC, "<cache>", S, Context, ES);
        if (ES != "")
          return std::make_error_code(std::errc::protocol_error);
        RHS = R.Mapping.RHS;
      }
      return std::error_code();
    } else {
      ++ExternalMisses;
      if (NoInfer) {
        RHS = 0;
        KV->hSet(LHSStr, "result", "");
        return std::error_code();
      }
      std::error_code EC = UnderlyingSolver->infer(BPCs, PCs, LHS, RHS, IC);
      std::string RHSStr;
      if (!EC && RHS) {
        RHSStr = GetReplacementRHSString(RHS, Context);
      }
      KV->hSet(LHSStr, "result", RHSStr);
      return EC;
    }
  }

  std::error_code isValid(const BlockPCs &BPCs,
                          const std::vector<InstMapping> &PCs,
                          InstMapping Mapping, bool &IsValid,
                          std::vector<std::pair<Inst *, llvm::APInt>> *Model)
  override {
    // N.B. we decided that since the important clients have moved to infer(),
    // we'll no longer support external caching for isValid()
    return UnderlyingSolver->isValid(BPCs, PCs, Mapping, IsValid, Model);
  }

  std::string getName() override {
    return UnderlyingSolver->getName() + " + external cache";
  }

  std::error_code nonNegative(const BlockPCs &BPCs,
                            const std::vector<InstMapping> &PCs,
                            Inst *LHS, APInt &NonNegative,
                            InstContext &IC) override {
    return UnderlyingSolver->nonNegative(BPCs, PCs, LHS, NonNegative, IC);
  }

  std::error_code Negative(const BlockPCs &BPCs,
                            const std::vector<InstMapping> &PCs,
                            Inst *LHS, APInt &Negative,
                            InstContext &IC) override {
    return UnderlyingSolver->Negative(BPCs, PCs, LHS, Negative, IC);
  }

  std::error_code knownBits(const BlockPCs &BPCs,
                            const std::vector<InstMapping> &PCs,
                            Inst *LHS, APInt &Zeros, APInt &Ones,
                            InstContext &IC) override {
    return UnderlyingSolver->knownBits(BPCs, PCs, LHS, Zeros, Ones, IC);
  }

  std::error_code powerTwo(const BlockPCs &BPCs,
                            const std::vector<InstMapping> &PCs,
                            Inst *LHS, APInt &PowerTwo,
                            InstContext &IC) override {
    return UnderlyingSolver->powerTwo(BPCs, PCs, LHS, PowerTwo, IC);
  }

  std::error_code testDemandedBits(const BlockPCs &BPCs,
                            const std::vector<InstMapping> &PCs,
                            Inst *LHS, APInt &DB,
                            InstContext &IC) override {
    return UnderlyingSolver->testDemandedBits(BPCs, PCs, LHS, DB, IC);
  }

  std::error_code nonZero(const BlockPCs &BPCs,
                            const std::vector<InstMapping> &PCs,
                            Inst *LHS, APInt &NonZero,
                            InstContext &IC) override {
    return UnderlyingSolver->nonZero(BPCs, PCs, LHS, NonZero, IC);
  }

  std::error_code signBits(const BlockPCs &BPCs,
                            const std::vector<InstMapping> &PCs,
                            Inst *LHS, unsigned &SignBits,
                            InstContext &IC) override {
    return UnderlyingSolver->signBits(BPCs, PCs, LHS, SignBits, IC);
  }

};

}

namespace souper {

Solver::~Solver() {}

std::unique_ptr<Solver> createBaseSolver(
    std::unique_ptr<SMTLIBSolver> SMTSolver, unsigned Timeout) {
  return std::unique_ptr<Solver>(new BaseSolver(std::move(SMTSolver), Timeout));
}

std::unique_ptr<Solver> createMemCachingSolver(
    std::unique_ptr<Solver> UnderlyingSolver) {
  return std::unique_ptr<Solver>(
      new MemCachingSolver(std::move(UnderlyingSolver)));
}

std::unique_ptr<Solver> createExternalCachingSolver(
    std::unique_ptr<Solver> UnderlyingSolver, KVStore *KV) {
  return std::unique_ptr<Solver>(
      new ExternalCachingSolver(std::move(UnderlyingSolver), KV));
}

}
