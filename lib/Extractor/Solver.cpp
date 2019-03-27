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
#include "llvm/ADT/SetVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Instruction.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/KnownBits.h"
#include "souper/Extractor/Solver.h"
#include "souper/Infer/AliveDriver.h"
#include "souper/Infer/ExhaustiveSynthesis.h"
#include "souper/Infer/InstSynthesis.h"
#include "souper/KVStore/KVStore.h"
#include "souper/Parser/Parser.h"

#include <unordered_map>

static const int MAX_TRIES = 30;

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
    cl::desc("Populate the external cache, but don't infer replacements (default=false)"),
    cl::init(false));
static cl::opt<bool> InferNop("souper-infer-nop",
    cl::desc("Infer that the output is the same as an input value (default=false)"),
    cl::init(false));
static cl::opt<bool> StressNop("souper-stress-nop",
    cl::desc("stress-test big queries in nop synthesis by always performing all of the small queries (slow!) (default=false)"),
    cl::init(false));
static cl::opt<int>MaxNops("souper-max-nops",
    cl::desc("maximum number of values from the LHS to try to use as the RHS (default=20)"),
    cl::init(20));
static cl::opt<bool> InferInts("souper-infer-iN",
    cl::desc("Infer iN integers for N>1 (default=true)"),
    cl::init(true));
static cl::opt<bool> InferInsts("souper-infer-inst",
    cl::desc("Infer instructions (default=false)"),
    cl::init(false));
static cl::opt<bool> EnableExhaustiveSynthesis("souper-exhaustive-synthesis",
    cl::desc("Use exaustive search for instruction synthesis (default=false)"),
    cl::init(false));
static cl::opt<int> MaxLHSSize("souper-max-lhs-size",
    cl::desc("Max size of LHS (in bytes) to put in external cache (default=1024)"),
    cl::init(1024));

class BaseSolver : public Solver {
  std::unique_ptr<SMTLIBSolver> SMTSolver;
  unsigned Timeout;

public:
  BaseSolver(std::unique_ptr<SMTLIBSolver> SMTSolver, unsigned Timeout)
      : SMTSolver(std::move(SMTSolver)), Timeout(Timeout) {}

  void findVarsAndWidth(Inst *node, std::map<std::string, unsigned> &var_vect) {
    if (node->K == Inst::Var) {
      std::string name = node->Name;
      var_vect[name] = node->Width;
    }
    for (auto const &Op : node->Ops) {
      findVarsAndWidth(Op, var_vect);
    }
  }

  Inst * set_traverse(Inst *node, unsigned bitPos, InstContext &IC, std::string var_name) {
    std::vector<Inst *> Ops;
    for (auto const &Op : node->Ops) {
      Ops.push_back(set_traverse(Op, bitPos, IC, var_name));
    }

    Inst *Copy = nullptr;
    if ((node->K == Inst::Var) && (node->Name == var_name)) {
      unsigned VarWidth = node->Width;
      APInt SetBit = APInt::getOneBitSet(VarWidth, bitPos);
      Inst *SetMask = IC.getInst(Inst::Or, VarWidth, {node, IC.getConst(SetBit)}); //xxxx || 0001

      Copy = SetMask;
    } else if (node->K == Inst::Var && node->Name != var_name) {
      return node;
    } else if (node->K == Inst::Const || node->K == Inst::UntypedConst) {
      return node;
    } else if (node->K == Inst::Phi) {
      auto BlockCopy = IC.createBlock(node->B->Preds);
      Copy = IC.getPhi(BlockCopy, Ops);
    } else {
      Copy = IC.getInst(node->K, node->Width, Ops);
    }
    assert(Copy);

    return Copy;
  }

  Inst * clear_traverse(Inst *node, unsigned bitPos, InstContext &IC, std::string var_name) {
    std::vector<Inst *> Ops;
    for (auto const &Op : node->Ops) {
      Ops.push_back(clear_traverse(Op, bitPos, IC, var_name));
    }

    Inst *Copy = nullptr;
    if (node->K == Inst::Var && node->Name == var_name) {
      unsigned VarWidth = node->Width;
      APInt ClearBit = getClearedBit(bitPos, VarWidth); //1110
      Inst *SetMask = IC.getInst(Inst::And, VarWidth, {node, IC.getConst(ClearBit)}); //xxxx && 1110

      Copy = SetMask;
    } else if (node->K == Inst::Var && node->Name != var_name) {
      return node;
    } else if (node->K == Inst::Const || node->K == Inst::UntypedConst) {
      return node;
    } else if (node->K == Inst::Phi) {
      auto BlockCopy = IC.createBlock(node->B->Preds);
      Copy = IC.getPhi(BlockCopy, Ops);
    } else {
      Copy = IC.getInst(node->K, node->Width, Ops);
    }
    assert(Copy);

    return Copy;
  }

  void plain_traverse(Inst *LHS) {
    if (!LHS) return;
    llvm::outs() << "Kind = " << Inst::getKindName(LHS->K) << ", Value = " << LHS->Val <<"\n";
    for (unsigned Op = 0; Op < LHS->Ops.size(); ++Op) {
      plain_traverse(LHS->Ops[Op]);
    }
  }

  // modified testDB w.r.t. InferNop bigquery logic
  bool testDB(const BlockPCs &BPCs,
              const std::vector<InstMapping> &PCs,
              Inst *LHS, Inst *NewLHS,
              InstContext &IC) {
    unsigned W = LHS->Width;
    Inst *Ne = IC.getInst(Inst::Ne, 1, {LHS, NewLHS});
    Inst *Ante = IC.getConst(APInt(1, 1));
    Ante = IC.getInst(Inst::And, 1, {Ante, Ne});
    APInt TrueGuess(1, 1, false);
    Inst *True = IC.getConst(TrueGuess);
    InstMapping Mapping(Ante, True);
/*
    llvm::outs() << "- - - -- - - - Original Tree is - - - - - - \n";
    plain_traverse(LHS);
    llvm::outs() << "- - - -- - - - New Tree is - - - - - - \n";
    plain_traverse(NewLHS);
*/

    //InstMapping Mapping(LHS, NewLHS);
    bool IsSat;
    std::string Query = BuildQuery(IC, BPCs, PCs, Mapping, 0, true);
    //llvm::outs() << "==== Query ==== \n" << Query << "\n";
    std::error_code EC = SMTSolver->isSatisfiable(Query,
                                                  IsSat, 0, 0, Timeout);
    if (EC)
      llvm::report_fatal_error("stopping due to error");
    //llvm::outs() << "Result of testDB IsSat = " << IsSat << "\n";
    return !IsSat;
  }

  std::error_code testDemandedBits(const BlockPCs &BPCs,
                              const std::vector<InstMapping> &PCs,
                              Inst *LHS, std::map<std::string, APInt> &ResDB_vect,
                              InstContext &IC) override {
    unsigned W = LHS->Width;
    std::map<Inst *, Inst *> InstCache;
    std::map<Block *, Block *> BlockCache;

    std::map<std::string, unsigned> vars_vect;
    findVarsAndWidth(LHS, vars_vect);

    // for each var
    for (std::map<std::string,unsigned>::iterator it = vars_vect.begin();
         it != vars_vect.end(); ++it) {
      // intialize ResultDB
       std::string var_name = it->first;
       unsigned var_width = vars_vect[var_name];
       APInt ResultDB = APInt::getNullValue(var_width);

      // for each bit of var
      for (unsigned bit=0; bit<var_width; bit++) {
        Inst *SetLHS = set_traverse(LHS, bit, IC, var_name);
/*
        llvm::errs()<<"R1-----\n";
        ReplacementContext RC1;
        RC1.printInst(SetLHS, llvm::errs(), true);
        ReplacementContext RC2;
        RC2.printInst(LHS, llvm::errs(), true);
        llvm::errs()<<"R1-----\n";
*/
        Inst *ClearLHS = clear_traverse(LHS, bit, IC, var_name);
/*
        llvm::errs()<<"R2-----\n";
        ReplacementContext RC3;
        RC3.printInst(ClearLHS, llvm::errs(), true);
        ReplacementContext RC4;
        RC4.printInst(LHS, llvm::errs(), true);
        llvm::errs()<<"R2-----\n";
*/
        if (testDB(BPCs, PCs, LHS, SetLHS, IC) && testDB(BPCs, PCs, LHS, ClearLHS, IC)) {
          // not-demanded
          ResultDB = ResultDB;
        } else {
          // demanded
          ResultDB |= APInt::getOneBitSet(var_width, bit);
        }
      }

      // verify if LHS has non-AllOnes demanded bits,
      // and, ResultDB for a variable has 1 in any bit-position for
      // which LHS->DB has 0 in it, conclude the bit to be non-demanded.
      if (!LHS->DemandedBits.isAllOnesValue()) {
        for (unsigned J=0; J<var_width; ++J) {
          if (ResultDB[J] == 1 && LHS->DemandedBits[J] == 0) {
            APInt ClearBit = getClearedBit(J, var_width);
            ResultDB &= ClearBit;
          }
        }
      }

      ResDB_vect[var_name] = ResultDB;
    }
    return std::error_code();
  }

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
    std::error_code EC = SMTSolver->isSatisfiable(BuildQuery(IC, BPCs, PCs, Mapping, 0),
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
    std::error_code EC = SMTSolver->isSatisfiable(BuildQuery(IC, BPCs, PCs, Mapping, 0),
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
    else {
      // if sign-bit is not guessed as 0 or 1, set non-negative 
      // signbit to 1, so that nothing is inferred by souper at the end
      //NonNegative = NonNegativeGuess;

      // test demandedbits
      if (!LHS->DemandedBits.isAllOnesValue()) {
	// nont demanded sign bit means non-neg
	if (LHS->DemandedBits[W-1] == 0)
          NonNegative = APInt::getNullValue(W);
	else
          NonNegative = NonNegativeGuess;
      } else {
        NonNegative = NonNegativeGuess;
      }
    }
    return std::error_code();
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
    // now verify if a bit is not guessed as zero and
    // it is not-demanded, conclude it as known zero.
    APInt ConstOne = APInt(W, 1);
    for (unsigned J=0; J<W; J++) {
      if (!LHS->DemandedBits.isAllOnesValue()) {
        if (!((LHS->DemandedBits.getHiBits(W-J) & ConstOne).getBoolValue()) &&
            !((Zeros.getHiBits(W-J) & ConstOne).getBoolValue())) {
          // make a zero guess
          Zeros = Zeros | APInt::getOneBitSet(W, J);
        }
      }
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
    std::error_code EC = SMTSolver->isSatisfiable(BuildQuery(IC, BPCs, PCs, Mapping, 0),
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
    std::error_code EC = SMTSolver->isSatisfiable(BuildQuery(IC, BPCs, PCs, Mapping, 0),
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
      std::error_code EC = SMTSolver->isSatisfiable(BuildQuery(IC, BPCs, PCs, Mapping, 0),
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
    // look for non-demanded bits in LHS, add up the number of non-demanded
    // bits to total number of signbits of LHS
    if (!LHS->DemandedBits.isAllOnesValue()) {
      for (unsigned bit=W-(SignBits+1); bit>=0; --bit) {
        if (LHS->DemandedBits[bit] == 0)
          SignBits++;
        else
          break;
      }
    }

    return std::error_code();
  }

  llvm::APInt getClearedBit(unsigned Pos, unsigned W) {
    APInt AllOnes = APInt::getAllOnesValue(W);
    AllOnes.clearBit(Pos);
    return AllOnes;
  }

  APInt getNextInputVal(Inst *Var,
                        Inst *LHSUB,
                        const BlockPCs &BPCs,
                        const std::vector<InstMapping> &PCs,
                        std::map<Inst *, std::vector<llvm::APInt>> &TriedVars,
                        InstContext &IC,
                        SMTLIBSolver *SMTSolver,
                        unsigned Timeout,
                        bool &HasNextInputValue) {

    // TODO
    // Specialize input values respecting blockpcs
    if (!BPCs.empty()) {
      HasNextInputValue = false;
      return APInt(Var->Width, 0);
    }

    HasNextInputValue = true;
    Inst *Ante = IC.getConst(APInt(1, true));
    Ante = IC.getInst(Inst::And, 1, {Ante, LHSUB});
    for (auto PC : PCs ) {
      Inst* Eq = IC.getInst(Inst::Eq, 1, {PC.LHS, PC.RHS});
      Inst* PCUB = getUBInstCondition(IC, Eq);
      Ante = IC.getInst(Inst::And, 1, {Ante, Eq});
      Ante = IC.getInst(Inst::And, 1, {Ante, PCUB});
    }

    // If a variable is neither found in PCs or TriedVar, return APInt(0)
    bool VarHasTried = TriedVars.find(Var) != TriedVars.end();
    if (!VarHasTried) {
      std::vector<Inst *> VarsInPCs;
      souper::findVars(Ante, VarsInPCs);
      if (std::find(VarsInPCs.begin(), VarsInPCs.end(), Var) == VarsInPCs.end()) {
        TriedVars[Var].push_back(APInt(Var->Width, 0));
        return APInt(Var->Width, 0);
      }
    }

    for (auto Value : TriedVars[Var]) {
      Inst* Ne = IC.getInst(Inst::Ne, 1, {Var, IC.getConst(Value)});
      Ante = IC.getInst(Inst::And, 1, {Ante, Ne});
    }

    InstMapping Mapping(Ante, IC.getConst(APInt(1, true)));

    std::vector<Inst *> ModelInsts;
    std::vector<llvm::APInt> ModelVals;
    std::string Query = BuildQuery(IC, {}, {}, Mapping, &ModelInsts, /*Negate=*/ true);

    bool PCQueryIsSat;
    std::error_code EC;
    EC = SMTSolver->isSatisfiable(Query, PCQueryIsSat, ModelInsts.size(), &ModelVals, Timeout);

    if (EC || !PCQueryIsSat) {
      if (VarHasTried) {
        // If we previously generated guesses on Var, and the query becomes
        // unsat, then clear the state and call the getNextInputVal() again to
        // get a new guess
        TriedVars.erase(Var);
        return getNextInputVal(Var, LHSUB, BPCs, PCs, TriedVars, IC,
                               SMTSolver, Timeout, HasNextInputValue);
      } else {
        // No guess record for Var found and query tells unsat, we can conclude
        // that no possible guess there
        HasNextInputValue = false;
        return APInt(Var->Width, 0);
      }
    }
    if (DebugLevel > 3)
      llvm::errs() << "Input guess SAT\n";
    for (unsigned I = 0 ; I != ModelInsts.size(); I++) {
      if (ModelInsts[I] == Var) {
        TriedVars[Var].push_back(ModelVals[I]);
        if (DebugLevel > 3)
          llvm::errs() << "Guess input value = " << ModelVals[I] << "\n";
        return ModelVals[I];
      }
    }

    llvm::report_fatal_error("Model does not contain the guess input variable");
  }

  std::error_code testRange(const BlockPCs &BPCs,
                            const std::vector<InstMapping> &PCs,
                            Inst *LHS, llvm::APInt &C,
                            llvm::APInt &X,
                            bool &IsFound,
                            InstContext &IC) {
    std::error_code EC;
    IsFound = false;
    unsigned W = LHS->Width;
    if (!LHS->DemandedBits.isAllOnesValue()) {
      LHS = IC.getInst(Inst::And, W, {LHS, IC.getConst(LHS->DemandedBits)});
    }

    Inst *SynthesisX = IC.createVar(W, ReservedConstPrefix);
    Inst *CVal = IC.getConst(C);
    Inst *LowerVal = SynthesisX;
    Inst *UpperValOverflow = IC.getInst(Inst::UAddWithOverflow, W + 1,
                                        {IC.getInst(Inst::Add, W, {LowerVal, CVal}),
                                            IC.getInst(Inst::UAddO, 1, {LowerVal, CVal})});

    Inst *SignBits = IC.getInst(Inst::ExtractValue, 1, {UpperValOverflow, IC.getUntypedConst(llvm::APInt(W, 1))});
    Inst *UpperVal = IC.getInst(Inst::ExtractValue, W, {UpperValOverflow, IC.getUntypedConst(llvm::APInt(W, 0))});

    Inst *GuessLowerPartNonWrapped = IC.getInst(Inst::Ule, 1, {LowerVal, LHS});
    Inst *GuessUpperPartNonWrapped = IC.getInst(Inst::Ult, 1, {LHS, UpperVal});

    // non-wrapped, x <= LHS < x+c
    Inst *GuessAnd = IC.getInst(Inst::And, 1, { GuessLowerPartNonWrapped, GuessUpperPartNonWrapped });
    // wrapped, LHS < x+c \/ LHS >= x
    Inst *GuessOr = IC.getInst(Inst::Or, 1, { GuessLowerPartNonWrapped, GuessUpperPartNonWrapped });

    // if x+c overflows, treat it as wrapped.
    Inst *Guess = IC.getInst(Inst::Select, 1, {SignBits, GuessOr, GuessAnd});

    std::vector<llvm::APInt> Tried;
    Inst *SubstAnte = IC.getConst(APInt(1, true));

    for (int i = 0 ; i < MAX_TRIES; i ++)  {
      bool IsSat;
      std::vector<Inst *> ModelInstsFirstQuery;
      std::vector<llvm::APInt> ModelValsFirstQuery;
      Inst *TriedAnte =   IC.getConst(APInt(1, true));

      for (auto T : Tried) {
        Inst *Ne = IC.getInst(Inst::Ne, W, {SynthesisX, IC.getConst(T)});
        TriedAnte = IC.getInst(Inst::And, 1, {TriedAnte, Ne});
      }
      Inst *Ante = IC.getInst(Inst::And, 1, {TriedAnte, Guess});

      Ante = IC.getInst(Inst::And, 1, {SubstAnte, Ante});

      InstMapping Mapping(Ante, IC.getConst(APInt(1, true)));

      std::string Query = BuildQuery(IC, BPCs, PCs, Mapping, &ModelInstsFirstQuery, true);
      EC = SMTSolver->isSatisfiable(Query, IsSat, ModelInstsFirstQuery.size(), &ModelValsFirstQuery, Timeout);

      if (EC)
        llvm::report_fatal_error("stopping due to error");

      if (!IsSat) {
        return EC;
      }

      // We found a model for a constant
      Inst *Const = 0;
      std::map<Inst *, llvm::APInt> ConstMap;
      for (unsigned J = 0; J != ModelInstsFirstQuery.size(); ++J) {
        if (ModelInstsFirstQuery[J]->Name == ReservedConstPrefix) {
          Const = IC.getConst(ModelValsFirstQuery[J]);
          Tried.push_back(Const->Val);
          ConstMap.insert(std::pair<Inst *, llvm::APInt>(ModelInstsFirstQuery[J], Const->Val));
          break;
        }
      }
      BlockPCs BPCsCopy;
      std::vector<InstMapping> PCsCopy;
      std::map<Inst *, Inst *> InstCache;
      std::map<Block *, Block *> BlockCache;
      auto I2 = getInstCopy(Guess, IC, InstCache, BlockCache, &ConstMap, false);
      separateBlockPCs(BPCs, BPCsCopy, InstCache, BlockCache, IC, &ConstMap, false);
      separatePCs(PCs, PCsCopy, InstCache, BlockCache, IC, &ConstMap, false);

      if (!Const)
        report_fatal_error("there must be a model for the constant");
      // Check if the constant is valid for all inputs
      std::vector<Inst *> ModelInstsSecondQuery;
      std::vector<llvm::APInt> ModelValsSecondQuery;

      InstMapping ConstMapping(I2, IC.getConst(APInt(1, true)));
      Query = BuildQuery(IC, BPCs, PCs, ConstMapping, &ModelInstsSecondQuery);
      //llvm::errs()<<Query;
      if (Query.empty())
        return std::make_error_code(std::errc::value_too_large);
      EC = SMTSolver->isSatisfiable(Query, IsSat, ModelInstsSecondQuery.size(), &ModelValsSecondQuery, Timeout);
      if (EC)
        llvm::report_fatal_error("stopping due to error");
      if (!IsSat) {
        X = Const->Val;
        IsFound = true;
        return EC;
      } else {
        std::map<Inst *, llvm::APInt> SubstConstMap;
        for (unsigned J = 0; J != ModelInstsFirstQuery.size(); ++J) {
          Inst* Var = ModelInstsFirstQuery[J];

          if (Var != SynthesisX) {
            SubstConstMap.insert(std::pair<Inst *, llvm::APInt>(Var, ModelValsFirstQuery[J]));
          }
          std::map<Inst *, Inst *> InstCache;
          std::map<Block *, Block *> BlockCache;
          SubstAnte = IC.getInst(Inst::And, 1,
                                 {getInstCopy(Guess, IC, InstCache, BlockCache, &SubstConstMap, false), SubstAnte});
          /*          ReplacementContext RC;
                      RC.printInst(SubstAnte, llvm::errs(), true);*/
        }
      }
    }
  }

  std::error_code range(const BlockPCs &BPCs,
                        const std::vector<InstMapping> &PCs,
                        Inst *LHS, llvm::ConstantRange &Range,
                        InstContext &IC) override {
    std::error_code EC;
    unsigned W = LHS->Width;
    APInt C(W, 1);
    APInt X;

    bool Found = false;
    EC = testRange(BPCs, PCs, LHS, C, X, Found, IC);
    if (Found) {
      Range = llvm::ConstantRange(X, X + 1);
      return EC;
    }

    C += 1;

    while (C.getBoolValue()) {
      Found = false;
      EC = testRange(BPCs, PCs, LHS, C, X, Found, IC);
      if (Found)
        break;
      C<<=1;
    }

    APInt L,R;
    L = C.getBoolValue() ? C.lshr(1) : APInt::getOneBitSet(W, W-1);
    R = C - 1;

    APInt BinSearchResultX;
    APInt BinSearchResultC;
    bool BinSearchHasResult = false;
    while (L.ule(R)) {
      APInt M = L + ((R - L)).lshr(1);
      APInt BinSearchX;
      EC = testRange(BPCs, PCs, LHS, M, BinSearchX, Found, IC);
      if (Found) {
        R = M - 1;

        // record result
        BinSearchResultX = BinSearchX;
        BinSearchResultC = M;
        BinSearchHasResult = true;
      } else {
        if (L == R) break;
        L = M + 1;
      }
    }
    if (BinSearchHasResult)
      Range = llvm::ConstantRange(BinSearchResultX, BinSearchResultX + BinSearchResultC);
    else if (C.getBoolValue()){
      Range = llvm::ConstantRange (X, X + C);
    } else {
      Range = llvm::ConstantRange (W, true);
    }

    return EC;
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

        if (UseAlive) {
          bool IsValid = isTransformationValid(Mapping.LHS, Mapping.RHS,
                                               PCs, IC);
          if (IsValid) {
            RHS = I;
            return std::error_code();
          }
          // TODO: Propagate errors from Alive backend, exit early for errors
        } else {
          std::string Query = BuildQuery(IC, BPCs, PCs, Mapping, 0);
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
    }

    if (InferInts && SMTSolver->supportsModels() && LHS->Width > 1) {
      std::vector<Inst *> ModelInsts;
      std::vector<llvm::APInt> ModelVals;
      Inst *I = IC.createVar(LHS->Width, "constant");
      InstMapping Mapping(LHS, I);

      if (UseAlive) {
        //Try to synthesize a constant at the root
        I = IC.createVar(LHS->Width, "reservedconst_0");

        Inst *Ante = IC.getConst(llvm::APInt(1, true));
        for (auto PC : PCs ) {
          Inst *Eq = IC.getInst(Inst::Eq, 1, {PC.LHS, PC.RHS});
          Ante = IC.getInst(Inst::And, 1, {Ante, Eq});
        }

        AliveDriver Synthesizer(LHS, Ante, IC);
        auto ConstantMap = Synthesizer.synthesizeConstants(I);
        if (ConstantMap.find(I) != ConstantMap.end()) {
          RHS = IC.getConst(ConstantMap[I]);
          return std::error_code();
        }
        // TODO: Propagate errors from Alive backend, exit early for errors
      } else {
        std::string Query = BuildQuery(IC, BPCs, PCs, Mapping, &ModelInsts, /*Negate=*/true);
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
          if (!Const)
            report_fatal_error("there must be a model for the constant");
          // Check if the constant is valid for all inputs
          InstMapping ConstMapping(LHS, Const);
          std::string Query = BuildQuery(IC, BPCs, PCs, ConstMapping, 0);
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
    }

    // Do not do further synthesis if LHS is harvested from uses.
    if (LHS->HarvestKind == HarvestType::HarvestedFromUse)
      return EC;

    if (InferNop) {
      std::vector<Inst *> Guesses;
      findCands(LHS, Guesses, /*WidthMustMatch=*/true, /*FilterVars=*/false, MaxNops);

      Inst *Ante = IC.getConst(APInt(1, true));
      BlockPCs BPCsCopy;
      std::vector<InstMapping> PCsCopy;
      for (auto I : Guesses) {
        // separate sub-expressions by copying vars
        std::map<Inst *, Inst *> InstCache;
        std::map<Block *, Block *> BlockCache;
        Inst *Ne = IC.getInst(Inst::Ne, 1, {getInstCopy(LHS, IC, InstCache, BlockCache, 0, true),
              getInstCopy(I, IC, InstCache, BlockCache, 0, true)});
        Ante = IC.getInst(Inst::And, 1, {Ante, Ne});
        separateBlockPCs(BPCs, BPCsCopy, InstCache, BlockCache, IC, 0, true);
        separatePCs(PCs, PCsCopy, InstCache, BlockCache, IC, 0, true);
      }

      // (LHS != i_1) && (LHS != i_2) && ... && (LHS != i_n) == true
      InstMapping Mapping(Ante, IC.getConst(APInt(1, true)));
      std::string Query = BuildQuery(IC, BPCsCopy, PCsCopy, Mapping, 0, /*Negate=*/true);
      if (Query.empty())
        return std::make_error_code(std::errc::value_too_large);
      bool BigQueryIsSat;
      EC = SMTSolver->isSatisfiable(Query, BigQueryIsSat, 0, 0, Timeout);
      if (EC)
        return EC;

      bool SmallQueryIsSat = true;
      if (StressNop || !BigQueryIsSat) {
        // find the nop
        for (auto I : Guesses) {
          InstMapping Mapping(LHS, I);
          std::string Query = BuildQuery(IC, BPCs, PCs, Mapping, 0);
          if (Query.empty())
            continue;
          EC = SMTSolver->isSatisfiable(Query, SmallQueryIsSat, 0, 0, Timeout);
          if (EC)
            return EC;
          if (!SmallQueryIsSat) {
            RHS = I;
            break;
          }
        }
      }

      if (!BigQueryIsSat && SmallQueryIsSat) {
        llvm::errs() << "*** oops ***\n";
        ReplacementContext C;
        llvm::errs() << GetReplacementLHSString(BPCs, PCs, LHS, C) << "\n";
        report_fatal_error("big query indicated a nop, but none was found");
      }
      if (BigQueryIsSat && !SmallQueryIsSat) {
        llvm::errs() << "*** oops ***\n";
        ReplacementContext C;
        llvm::errs() << GetReplacementLHSString(BPCs, PCs, LHS, C) << "\n";
        report_fatal_error("big query did not indicate a nop, but one was found");
      }

      if (!SmallQueryIsSat)
        return EC;
    }

    if(SMTSolver->supportsModels()) {
      if (EnableExhaustiveSynthesis) {
        ExhaustiveSynthesis ES;
        EC = ES.synthesize(SMTSolver.get(), BPCs, PCs, LHS, RHS, IC, Timeout);
        if (EC || RHS)
          return EC;
      } else if (InferInsts) {
        InstSynthesis IS;
        EC = IS.synthesize(SMTSolver.get(), BPCs, PCs, LHS, RHS, IC, Timeout);
        if (EC || RHS)
          return EC;
      }
    }

    RHS = 0;
    return EC;
  }

  std::error_code isValid(InstContext &IC, const BlockPCs &BPCs,
                          const std::vector<InstMapping> &PCs,
                          InstMapping Mapping, bool &IsValid,
                          std::vector<std::pair<Inst *, llvm::APInt>> *Model)
  override {
    if (UseAlive) {
      IsValid = isTransformationValid(Mapping.LHS, Mapping.RHS, PCs, IC);
      return std::error_code();
    }
    std::string Query;
    if (Model && SMTSolver->supportsModels()) {
      std::vector<Inst *> ModelInsts;
      std::string Query = BuildQuery(IC, BPCs, PCs, Mapping, &ModelInsts);
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
      std::string Query = BuildQuery(IC, BPCs, PCs, Mapping, 0);
      if (Query.empty())
        return std::make_error_code(std::errc::value_too_large);
      bool IsSat;
      std::error_code EC = SMTSolver->isSatisfiable(Query, IsSat, 0, 0, Timeout);
      IsValid = !IsSat;
      return EC;
    }
  }

  bool testKnown(const BlockPCs &BPCs,
                 const std::vector<InstMapping> &PCs,
                 APInt &Zeros, APInt &Ones, Inst *LHS,
                 InstContext &IC) {
    unsigned W = LHS->Width;
    Inst *Mask = IC.getConst(Zeros | Ones);
    InstMapping Mapping(IC.getInst(Inst::And, W, { LHS, Mask }), IC.getConst(Ones));
    bool IsSat;
    //Mapping.LHS->DemandedBits = APInt::getAllOnesValue(Mapping.LHS->Width);
    std::error_code EC = SMTSolver->isSatisfiable(BuildQuery(IC, BPCs, PCs, Mapping, 0),
                                                  IsSat, 0, 0, Timeout);
    if (EC)
      llvm::report_fatal_error("stopping due to error");
    return !IsSat;
  }


  llvm::KnownBits findKnownBitsUsingSolver(const BlockPCs &BPCs,
                                           const std::vector<InstMapping> &PCs,
                                           Inst *LHS, InstContext &IC) override {
    unsigned W = LHS->Width;
    auto R = llvm::KnownBits(W);
    for (unsigned Pos = 0; Pos < W; Pos++) {
      APInt ZeroGuess = R.Zero | APInt::getOneBitSet(W, Pos);
      if (testKnown(BPCs, PCs, ZeroGuess, R.One, LHS, IC)) {
        R.Zero = ZeroGuess;
	continue;
      }
      APInt OneGuess = R.One | APInt::getOneBitSet(W, Pos);
      if (testKnown(BPCs, PCs, R.Zero, OneGuess, LHS, IC)) {
	R.One = OneGuess;
        continue;
      }
    }
    return R;
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

  std::error_code isValid(InstContext &IC, const BlockPCs &BPCs,
                          const std::vector<InstMapping> &PCs,
                          InstMapping Mapping, bool &IsValid,
                          std::vector<std::pair<Inst *, llvm::APInt>> *Model)
    override {
    // TODO: add caching support for models.
    if (Model)
      return UnderlyingSolver->isValid(IC, BPCs, PCs, Mapping, IsValid, Model);

    std::string Repl = GetReplacementString(BPCs, PCs, Mapping);
    const auto &ent = IsValidCache.find(Repl);
    if (ent == IsValidCache.end()) {
      ++MemMissesIsValid;
      std::error_code EC = UnderlyingSolver->isValid(IC, BPCs, PCs,
                                                     Mapping, IsValid, 0);
      IsValidCache.emplace(Repl, std::make_pair(EC, IsValid));
      return EC;
    } else {
      ++MemHitsIsValid;
      IsValid = ent->second.second;
      return ent->second.first;
    }
  }

  llvm::KnownBits findKnownBitsUsingSolver(const BlockPCs &BPCs,
                                           const std::vector<InstMapping> &PCs,
                                           Inst *LHS, InstContext &IC) override {
    return UnderlyingSolver->findKnownBitsUsingSolver(BPCs, PCs, LHS, IC);
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

  std::error_code range(const BlockPCs &BPCs,
                            const std::vector<InstMapping> &PCs,
                            Inst *LHS, llvm::ConstantRange &Range,
                            InstContext &IC) override {
    return UnderlyingSolver->range(BPCs, PCs, LHS, Range, IC);
  }

  std::error_code testDemandedBits(const BlockPCs &BPCs,
                            const std::vector<InstMapping> &PCs,
                            Inst *LHS, std::map<std::string,APInt> &DB_vect,
                            InstContext &IC) override {
    return UnderlyingSolver->testDemandedBits(BPCs, PCs, LHS, DB_vect, IC);
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

  std::error_code isValid(InstContext &IC, const BlockPCs &BPCs,
                          const std::vector<InstMapping> &PCs,
                          InstMapping Mapping, bool &IsValid,
                          std::vector<std::pair<Inst *, llvm::APInt>> *Model)
  override {
    // N.B. we decided that since the important clients have moved to infer(),
    // we'll no longer support external caching for isValid()
    return UnderlyingSolver->isValid(IC, BPCs, PCs, Mapping, IsValid, Model);
  }

  llvm::KnownBits findKnownBitsUsingSolver(const BlockPCs &BPCs,
                                           const std::vector<InstMapping> &PCs,
                                           Inst *LHS, InstContext &IC) override {
    return UnderlyingSolver->findKnownBitsUsingSolver(BPCs, PCs, LHS, IC);
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

  std::error_code range(const BlockPCs &BPCs,
                            const std::vector<InstMapping> &PCs,
                            Inst *LHS, llvm::ConstantRange &Range,
                            InstContext &IC) override {
    return UnderlyingSolver->range(BPCs, PCs, LHS, Range, IC);
  }

  std::error_code testDemandedBits(const BlockPCs &BPCs,
                            const std::vector<InstMapping> &PCs,
                            Inst *LHS, std::map<std::string, APInt> &DB_vect,
                            InstContext &IC) override {
    return UnderlyingSolver->testDemandedBits(BPCs, PCs, LHS, DB_vect, IC);
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
