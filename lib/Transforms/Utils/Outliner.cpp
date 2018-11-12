//===- Outliner.cpp - Generic outliner interface --------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements an interface for outlining congruent sequences.
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Utils/Outliner.h"
#include "llvm/ADT/BitVector.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/PriorityQueue.h"
#include "llvm/Analysis/ProfileSummaryInfo.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"

using namespace llvm;

static cl::opt<bool> AllowODR(
    "cso-allow-odr", cl::init(false), cl::Hidden,
    cl::desc("Allow outlining from linkonce_odr and weak_odr functions."));

static cl::opt<bool> DumpCC(
    "cso-dump-cc", cl::init(false), cl::Hidden,
    cl::desc("Dump information about the congruent between instructions."));

// Suffix array implementation.
namespace {
/// Compute the suffix array.
//  Basic adapted implementation of SA-IS algorithm.
class SuffixArray {
public:
  // Compute the suffix array of S with given alphabet size AlphabetSize
  // and store the result in SA
  static std::vector<int> compute(std::vector<unsigned> &S) {
    // REQUIRED: N-1 must be 0 to act as a sentinel for the suffix array
    // algorithm.
    S.push_back(0);

    // Get the alphabet size of the unsigned vector.
    unsigned AlphabetSize = 0;
    for (unsigned CC : S)
      if (CC > AlphabetSize)
        AlphabetSize = CC;
    ++AlphabetSize;

    SuffixArray SACtr(S.size());
    SACtr.computeSAIS(ArrayRef<unsigned>(S), S.size(), AlphabetSize);
    return std::move(SACtr.SA);
  }

private:
  SuffixArray(size_t ArraySize) { SA.resize(ArraySize); }

  template <typename T>
  void computeSAIS(ArrayRef<T> S, int N, unsigned AlphabetSize) {
    // Bitvector for LS-type array.
    BitVector LTypeArray(N);

    // Classify each character from S as either LType or SType.
    LTypeArray.set(N - 1);
    for (int i = N - 3, e = 0; i >= e; --i) {
      // S(i) is type S iff: S(i) < S(i+1) or S(i)==S(i+1) and S(i+1) is type
      // S
      if (S[i] < S[i + 1] || (S[i] == S[i + 1] && LTypeArray.test(i + 1)))
        LTypeArray.set(i);
    }

    // Stage 1: Reduce the problem and bucket sort all S-substrings.
    Bucket.resize(AlphabetSize + 1);
    // Get the bucket ends.
    getBuckets(S, true, N, AlphabetSize);
    for (int i = 0; i < N; ++i)
      SA[i] = -1;
    for (int i = 1; i < N; ++i)
      if (isLMS(i, LTypeArray))
        SA[--Bucket[S[i]]] = i;
    induceSA(S, LTypeArray, N, AlphabetSize);
    Bucket.clear();

    // Compact the sorted substrings into the first N1 items of the suffix
    // array.
    int N1 = 0;
    for (int i = 0; i < N; ++i)
      if (isLMS(SA[i], LTypeArray))
        SA[N1++] = SA[i];

    // Find the lexicographic names of the substrings.
    for (int i = N1; i < N; ++i)
      SA[i] = -1;
    int Name = 0, Prev = -1;
    for (int i = 0; i < N1; ++i) {
      int Pos = SA[i];
      for (int d = 0; d < N; ++d) {
        if (Prev == -1 || S[Pos + d] != S[Prev + d] ||
            LTypeArray.test(Pos + d) != LTypeArray.test(Prev + d)) {
          ++Name;
          Prev = Pos;
          break;
        }
        if (d > 0 &&
            (isLMS(Pos + d, LTypeArray) || isLMS(Prev + d, LTypeArray)))
          break;
      }
      Pos = (Pos % 2 == 0) ? Pos / 2 : (Pos - 1) / 2;
      SA[N1 + Pos] = Name - 1;
    }
    for (int i = N - 1, j = i; i >= N1; --i)
      if (SA[i] >= 0)
        SA[j--] = SA[i];

    // Stage 2: Solve the reduced problem.
    // If the names aren't unique enough yet, we recurse until they are.
    size_t S1Start = N - N1;
    int *S1 = SA.data() + S1Start;
    if (Name < N1) {
      computeSAIS(ArrayRef<int>(S1, N1), N1, Name - 1);
    } else {
      // Otherwise we can compute the suffix array directly.
      for (int i = 0; i < N1; ++i)
        SA[S1[i]] = i;
    }

    // Stage 3: Induce the result from the reduced solution.
    Bucket.resize(AlphabetSize + 1);
    // Place the LMS characters into their respective buckets.
    getBuckets(S, true, N, AlphabetSize);
    // Get P1.
    for (int i = 1, j = 0; i < N; ++i)
      if (isLMS(i, LTypeArray))
        S1[j++] = i;
    // Get the index in S.
    for (int i = 0; i < N1; ++i)
      SA[i] = S1[SA[i]];
    // Initialize the suffix array from N1 to N - 1.
    for (int i = N1; i < N; ++i)
      SA[i] = -1;
    for (int i = N1 - 1; i >= 0; --i) {
      int j = SA[i];
      SA[i] = -1;
      SA[--Bucket[S[j]]] = j;
    }
    induceSA(S, LTypeArray, N, AlphabetSize);
  }

  // Check to see if S(Idx) is a left most S-type character.
  bool isLMS(int Idx, BitVector &LTypeArray) {
    return Idx > 0 && LTypeArray.test(Idx) && !LTypeArray.test(Idx - 1);
  }
  template <typename T>
  void getBuckets(ArrayRef<T> S, bool End, unsigned N, unsigned AlphabetSize) {
    // Clear buckets.
    Bucket.assign(AlphabetSize + 1, 0);
    // Compute the size of each bucket.
    for (size_t i = 0, e = S.size(); i < e; ++i)
      ++Bucket[S[i]];
    int Sum = 0;
    if (!End) {
      for (size_t i = 0, e = AlphabetSize + 1; i < e; ++i) {
        Sum += Bucket[i];
        Bucket[i] = Sum - Bucket[i];
      }
    } else {
      for (size_t i = 0; i <= AlphabetSize; ++i)
        Bucket[i] = Sum += Bucket[i];
    }
  }

  // Compute SA1
  template <typename T>
  void induceSA(ArrayRef<T> S, BitVector &LTypeArray, unsigned N,
                unsigned AlphabetSize) {
    // Induce SA1
    getBuckets(S, false, N, AlphabetSize);
    for (size_t i = 0; i < N; ++i) {
      int j = SA[i] - 1;
      if (j >= 0 && !LTypeArray.test(j))
        SA[Bucket[S[j]]++] = j;
    }
    // Induce Sas
    getBuckets(S, true, N, AlphabetSize);
    for (ssize_t i = N - 1; i >= 0; --i) {
      int j = SA[i] - 1;
      if (j >= 0 && LTypeArray.test(j))
        SA[--Bucket[S[j]]] = j;
    }
  }
  std::vector<int> SA;
  std::vector<int> Bucket;
};
// Construct the LCP array for a given suffix array SA and string S.
static std::vector<int> computeLCP(ArrayRef<unsigned> S, ArrayRef<int> SA) {
  int N = S.size();
  std::vector<int> LCP(N), Rank(N);
  for (int i = 0; i < N; ++i)
    Rank[SA[i]] = i;
  for (int i = 0, k = 0; i < N; ++i) {
    if (Rank[i] == N - 1) {
      k = 0;
      continue;
    }
    int j = SA[Rank[i] + 1];
    while (i + k < N && j + k < N && S[i + k] == S[j + k])
      ++k;
    LCP[Rank[i]] = k;
    if (k > 0)
      --k;
  }
  return LCP;
}
} // namespace

// Candidate Selection.
bool llvm::findSequentialCandidates(
    function_ref<bool(ArrayRef<unsigned>, unsigned)> PrePruneFn,
    std::vector<unsigned> &Vec, unsigned MinInstructionLen,
    unsigned MinOccurrences, std::vector<Candidate> &CL) {
  CL.clear();

  // Build the suffix array and longest common prefix array.
  std::vector<int> SuffixArr = SuffixArray::compute(Vec);
  std::vector<int> LcpArr = computeLCP(Vec, SuffixArr);

  // An interval tree of our current candidates.
  BitVector CandidateInterval(Vec.size());

  // Walk the suffix array to build potential candidates.
  SmallDenseSet<size_t, 16> FailedOccurrences;
  size_t PrevSize = 0;
  std::vector<unsigned> Occurrences;
  for (size_t i = 1, e = SuffixArr.size(); i < e; ++i) {
    size_t Size = LcpArr[i];

    // Preskip invalid size.
    if (Size < MinInstructionLen) {
      PrevSize = 0;
      continue;
    }

    size_t OccurIdx = SuffixArr[i];

    // We have already matched against this size.
    if (PrevSize >= Size) {
      PrevSize = Size;
      continue;
    }

    // Create a new interval tree with our current candidate to pre prune
    //   overlaps.
    Occurrences.clear();
    CandidateInterval.set(OccurIdx, OccurIdx + Size);
    Occurrences.push_back(OccurIdx);
    FailedOccurrences.clear();
    bool HasPreviousSharedOccurrence = false;

    // Continuously consider potentital chain sizes for this candidate until
    // they are no longer profitable.
    size_t OrigSize = Size, LastValidSize = 0;
    for (size_t SizeFromIdx = i, AugmentAmount = 0;
         Size >= MinInstructionLen;) {
      bool AddedNewOccurrence = false;

      // Augment the candidate set by the change in size from the
      // last iteration.
      if (AugmentAmount > 0)
        for (size_t Idx : Occurrences)
          CandidateInterval.reset(Idx + Size, Idx + Size + AugmentAmount);
      LastValidSize = Size;

      // After augmenting the candidate set, there may be new candidates that
      // no longer overlap with any of the others currently being considered.
      for (auto It = FailedOccurrences.begin(), E = FailedOccurrences.end();
           It != E;) {
        size_t Idx = *It;
        ++It;
        if (CandidateInterval.find_first_in(Idx, Idx + Size) != -1)
          continue;
        FailedOccurrences.erase(Idx);
        CandidateInterval.set(Idx, Idx + Size);
        Occurrences.push_back(Idx);
        AddedNewOccurrence = true;
      }

      // Count the number of occurrences.
      for (size_t j = i + Occurrences.size(); j < e; ++j) {
        // The longest common prefix must be able to hold our size.
        if ((size_t)LcpArr[j - 1] < Size)
          break;

        // Check to see if this candidate overlaps with any of our currently
        // considered candidates. If it doesn't we add it to our current set.
        size_t JIdx = SuffixArr[j];
        if (CandidateInterval.find_first_in(JIdx, JIdx + Size) == -1) {
          CandidateInterval.set(JIdx, JIdx + Size);
          Occurrences.push_back(JIdx);
          AddedNewOccurrence = true;
        } else {
          FailedOccurrences.insert(JIdx);
	}

        // If our next size is less than the current, we won't get any more
        //  candidates for this chain.
        if ((size_t)LcpArr[j] < Size)
          break;
      }

      // If we added a new candidate and we have enough to satisfy our
      // constraints then we build a new outline chain candidate.
      if (AddedNewOccurrence && Occurrences.size() >= MinOccurrences) {
        // Recheck the prune size each iteration.
        if (!PrePruneFn || !PrePruneFn(Occurrences, Size)) {
          // Cache shared sizes between candidates chains to make analysis
          // easier.
          if (HasPreviousSharedOccurrence)
            CL.back().SharedSizeWithNext = Size;
          else
            HasPreviousSharedOccurrence = true;
          // Build new function with candidate sequence.
          CL.emplace_back(CL.size(), Size, Occurrences);
        }
      }

      // Find the next size to consider for this candidate.
      for (size_t NewSizeE = e - 1; ++SizeFromIdx < NewSizeE;) {
        size_t NewSize = static_cast<size_t>(LcpArr[SizeFromIdx]);
        if (NewSize < Size) {
          AugmentAmount = Size - NewSize;
          Size = NewSize;
          break;
        }
      }

      // If we have already encountered a greater size, then the new size
      //  was either invalid or we've already considered this size but
      //  with more candidates.
      if (Size == LastValidSize || Size <= PrevSize)
        break;
    }
    for (unsigned Idx : Occurrences)
      CandidateInterval.reset(Idx, Idx + LastValidSize);
    PrevSize = OrigSize;
  }
  return !CL.empty();
}

// Candidate Pruning.
bool llvm::pruneSequentialCandidateList(
    MutableArrayRef<Candidate> CL, unsigned NumMappedInstructions) {
  // Helper comparator for candidate indexes.
  struct Comparator {
    Comparator(ArrayRef<Candidate> CL) : CL(CL) {}
    bool operator()(unsigned L, unsigned R) {
      return CL[L].Benefit < CL[R].Benefit;
    }
    ArrayRef<Candidate> CL;
  };

  // Build a priority worklist for the valid candidates.
  std::vector<unsigned> OriginalSetOfValidCands;
  OriginalSetOfValidCands.reserve(CL.size());
  for (unsigned i = 0, e = CL.size(); i < e; ++i)
    if (CL[i].isValid())
      OriginalSetOfValidCands.push_back(i);

  // Priority queue of the most profitable candidates.
  Comparator C(CL);
  PriorityQueue<unsigned, std::vector<unsigned>, Comparator> MostBenefitial(
      C, OriginalSetOfValidCands);

  // BitVector of all of the occurrence instructions that have been tagged
  //  as profitable to outline. We use this to prune less beneficial
  //  occurrences.
  BitVector InsertedOccurrences(NumMappedInstructions);
  bool HasProfitableCandidate = false;
  while (!MostBenefitial.empty()) {
    // Get the next most benefical candidate.
    unsigned CandIdx = MostBenefitial.top();
    MostBenefitial.pop();
    Candidate &C = CL[CandIdx];

    // Check overlaps.
    bool PrunedAnOccurrence = false;
    for (ssize_t i = C.size() - 1; i >= 0; --i) {
      unsigned Occur = C.getOccurrence(i);
      if (InsertedOccurrences.find_first_in(Occur, Occur + C.Len) == -1)
        continue;
      if (C.Benefit < C.BenefitPerOccur) {
        C.invalidate();
        break;
      }
      C.Benefit -= C.BenefitPerOccur;
      C.removeOccurrence(i);
      PrunedAnOccurrence = true;
    }

    // Add valid occurrences if this candidate is still profitable.
    if (!C.isValid())
      continue;

    // If we pruned an occurrences, we readd the candidate
    //  so that we can get the candidate with the next highest benefit.
    if (PrunedAnOccurrence) {
      MostBenefitial.push(CandIdx);
      continue;
    }

    // Tag our valid occurrences.
    for (unsigned Occur : C)
      InsertedOccurrences.set(Occur, Occur + C.Len);
    HasProfitableCandidate = true;
  }
  return HasProfitableCandidate;
}

// Mapping an IR module for outlining.

/// Expression with relaxed equivalency constraints.
class RelaxedExpression {
public:
  /// A special state for special equivalence constraints.
  enum SpecialState { StructGep, ConstrainedCall, None };

  RelaxedExpression(Instruction &I)
      : Inst(&I), SS(SpecialState::None), HashVal(0) {
    // Check the special state.
    CallSite CS(Inst);
    if (CS) {
      // Don't take the address of inline asm calls.
      if (CS.isInlineAsm() || CS.isInvoke()) {
        SS = RelaxedExpression::ConstrainedCall;
      } else if (Function *F = CS.getCalledFunction()) {
	// Intrinsics and functions without exact definitions can not
	// have their address taken.
        if (!canTakeFnAddress(F))
          SS = RelaxedExpression::ConstrainedCall;
      }
    } else if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(&I)) {
      // Struct geps require constant indices.
      if (gepContainsStructType(GEP))
        SS = RelaxedExpression::StructGep;
    }
  }
  bool equals(const RelaxedExpression &OE) const {
    if (SS != OE.SS)
      return false;
    // Handle calls separately to allow for mismatched tail calls.
    CallSite CS(Inst);
    if (CS) {
      CallSite RCS(OE.Inst);
      if (CS.getNumArgOperands() != RCS.getNumArgOperands())
        return false;
      if (CS.getCallingConv() != RCS.getCallingConv() ||
          CS.getAttributes() != RCS.getAttributes())
        return false;
      if (CS.isInvoke()) {
        InvokeInst *L = cast<InvokeInst>(Inst), *R = cast<InvokeInst>(OE.Inst);
        if (!L->hasIdenticalOperandBundleSchema(*R))
          return false;
      } else {
        CallInst *L = cast<CallInst>(Inst), *R = cast<CallInst>(OE.Inst);
        if (!L->hasIdenticalOperandBundleSchema(*R))
          return false;
      }
    } else if (isa<BitCastInst>(Inst)) {
      return Inst->getType() == OE.Inst->getType();
    } else if (!Inst->isSameOperationAs(OE.Inst,
					Instruction::CompareIgnoringAlignment)) {
      return false;
    }
    return checkSpecialEquivalence(OE);
  }
  hash_code getComputedHash() const {
    if (static_cast<unsigned>(HashVal) == 0)
      HashVal = getHashValue();
    return HashVal;
  }
  hash_code getHashValue() const {
    SmallVector<size_t, 8> HashRange;
    HashRange.push_back(SS);
    HashRange.push_back(Inst->getNumOperands());
    HashRange.push_back(reinterpret_cast<size_t>(Inst->getType()));
    if (!isa<BitCastInst>(Inst))
      for (auto &Op : Inst->operands())
        HashRange.emplace_back(reinterpret_cast<size_t>(Op->getType()));
    return hash_combine_range(HashRange.begin(), HashRange.end());
  }

private:
  // Check to see if we can take the address of a function.
  bool canTakeFnAddress(Function *F) const {
    // A function marked 'alwaysinline' with available_externally linkage can't
    // have its address taken. Doing so would create an undefined external ref
    // to the function, which would fail to link.
    bool HasAvailableExternallyLinkage = F->hasAvailableExternallyLinkage();
    if (HasAvailableExternallyLinkage &&
        F->hasFnAttribute(Attribute::AlwaysInline))
      return false;
    return F->hasExactDefinition() || F->hasAddressTaken() ||
           F->hasLinkOnceLinkage();
  }
  // Special checks for instructions that have non generic equivalency.
  bool checkSpecialEquivalence(const RelaxedExpression &Other) const {
    const Instruction *OE = Other.Inst;
    switch (Inst->getOpcode()) {
    case Instruction::ShuffleVector: {
      // LangRef : The shuffle mask operand is required to be a
      // constant vector with either constant integer or undef values.
      return Inst->getOperand(2) == OE->getOperand(2);
    }
    case Instruction::Call:
    case Instruction::Invoke: {
      CallSite LCS(Inst);
      CallSite RCS(const_cast<Instruction *>(OE));
      if (SS == ConstrainedCall)
        return checkConstrainedCallEquivalence(LCS, RCS);
      return LCS.getFunctionType() == RCS.getFunctionType();
    }
    case Instruction::GetElementPtr: {
      // Struct indices must be constant.
      if (SS == StructGep)
        return compareStructIndices(cast<GetElementPtrInst>(Inst),
                                    cast<GetElementPtrInst>(OE));
      break;
    }
    default:
      break;
    }
    return true;
  }
  bool checkConstrainedCallEquivalence(const CallSite &LCS,
                                       const CallSite &RCS) const {
    const Value *CIVal = LCS.getCalledValue();
    if (CIVal != RCS.getCalledValue())
      return false;
    if (const Function *CalledII = dyn_cast<Function>(CIVal)) {
      switch (CalledII->getIntrinsicID()) {
      case Intrinsic::memmove:
      case Intrinsic::memcpy:
      case Intrinsic::memset:
        // Size.
        return LCS.getArgOperand(2) == RCS.getArgOperand(2) &&
               // Volatile flag.
               LCS.getArgOperand(3) == RCS.getArgOperand(3);
      case Intrinsic::objectsize:
        // Min.
        return LCS.getArgOperand(1) == RCS.getArgOperand(1) &&
               // Null unknown.
               LCS.getArgOperand(2) == RCS.getArgOperand(2);
      case Intrinsic::expect:
        // Expected value.
        return LCS.getArgOperand(1) == RCS.getArgOperand(1);
      case Intrinsic::prefetch:
        // RW.
        return LCS.getArgOperand(1) == RCS.getArgOperand(1) &&
               // Locality.
               LCS.getArgOperand(2) == RCS.getArgOperand(2) &&
               // Cache Type.
               LCS.getArgOperand(3) == RCS.getArgOperand(3);
      case Intrinsic::ctlz:
      case Intrinsic::cttz:
        // Is Zero Undef.
        return LCS.getArgOperand(1) == RCS.getArgOperand(1);
      case Intrinsic::invariant_start:
        // Size.
        return LCS.getArgOperand(0) == RCS.getArgOperand(0);
      default:
        break;
      }
    }
    return true;
  }
  bool compareStructIndices(GetElementPtrInst *L,
                            const GetElementPtrInst *R) const {
    gep_type_iterator LIt = gep_type_begin(L), LE = gep_type_end(L);
    gep_type_iterator RIt = gep_type_begin(R);
    for (; LIt != LE; ++LIt, ++RIt) {
      if (LIt.isStruct() && LIt.getOperand() != RIt.getOperand())
        return false;
    }
    return true;
  }
  // Check to see if the provided gep GEP indexes a struct type.
  bool gepContainsStructType(GetElementPtrInst *GEP) {
    gep_type_iterator It = gep_type_begin(GEP), E = gep_type_end(GEP);
    for (; It != E; ++It)
      if (It.isStruct())
        return true;
    return false;
  }

  Instruction *Inst;
  SpecialState SS;
  mutable hash_code HashVal;
};

// DenseMapInfo for the relaxed expression class.
template <> struct llvm::DenseMapInfo<const RelaxedExpression *> {
  static const RelaxedExpression *getEmptyKey() {
    auto Val = static_cast<uintptr_t>(-1);
    Val <<=
        PointerLikeTypeTraits<const RelaxedExpression *>::NumLowBitsAvailable;
    return reinterpret_cast<const RelaxedExpression *>(Val);
  }
  static const RelaxedExpression *getTombstoneKey() {
    auto Val = static_cast<uintptr_t>(~1U);
    Val <<=
        PointerLikeTypeTraits<const RelaxedExpression *>::NumLowBitsAvailable;
    return reinterpret_cast<const RelaxedExpression *>(Val);
  }
  static unsigned getHashValue(const RelaxedExpression *E) {
    return E->getComputedHash();
  }
  static bool isEqual(const RelaxedExpression *LHS,
                      const RelaxedExpression *RHS) {
    if (LHS == RHS)
      return true;
    if (LHS == getTombstoneKey() || RHS == getTombstoneKey() ||
        LHS == getEmptyKey() || RHS == getEmptyKey())
      return false;
    if (LHS->getComputedHash() != RHS->getComputedHash())
      return false;
    return LHS->equals(*RHS);
  }
};

// How an instruction is mapped.
enum class IRInstructionMapType { Invalid, Ignored, Valid };

// Checks to see if a provided instruction I can be mapped.
IRInstructionMapType getInstrMapType(Instruction *I) {
  CallSite CS(I);
  if (CS) {
    // Be very conservative about musttail because it has additional
    // guarantees that must be met.
    if (CS.isMustTailCall())
      return IRInstructionMapType::Invalid;
    // Be conservative about return twice and inalloca calls.
    if (CS.hasFnAttr(Attribute::ReturnsTwice) || CS.hasInAllocaArgument())
      return IRInstructionMapType::Invalid;
    switch (CS.getIntrinsicID()) {
      // We ignore debug intrinsics.
    case Intrinsic::dbg_declare:
    case Intrinsic::dbg_value:
      // As well as lifetime instructions.
    case Intrinsic::lifetime_start:
    case Intrinsic::lifetime_end:
      return IRInstructionMapType::Ignored;
      // Misc intrinsics that we handle.
    case Intrinsic::objectsize:
    case Intrinsic::expect:
    case Intrinsic::prefetch:
    case Intrinsic::trap:
      // Invariants.
    case Intrinsic::invariant_start:
      // Overflow intrinsics.
    case Intrinsic::sadd_with_overflow:
    case Intrinsic::uadd_with_overflow:
    case Intrinsic::ssub_with_overflow:
    case Intrinsic::usub_with_overflow:
    case Intrinsic::smul_with_overflow:
    case Intrinsic::umul_with_overflow:
      // Lib C functions are fine.
    case Intrinsic::memcpy:
    case Intrinsic::memmove:
    case Intrinsic::memset:
    case Intrinsic::sqrt:
    case Intrinsic::pow:
    case Intrinsic::powi:
    case Intrinsic::sin:
    case Intrinsic::cos:
    case Intrinsic::exp:
    case Intrinsic::exp2:
    case Intrinsic::log:
    case Intrinsic::log2:
    case Intrinsic::log10:
    case Intrinsic::fma:
    case Intrinsic::fabs:
    case Intrinsic::minnum:
    case Intrinsic::maxnum:
    case Intrinsic::copysign:
    case Intrinsic::floor:
    case Intrinsic::ceil:
    case Intrinsic::trunc:
    case Intrinsic::rint:
    case Intrinsic::nearbyint:
    case Intrinsic::round:
      // Bit manipulation intrinsics.
    case Intrinsic::bitreverse:
    case Intrinsic::bswap:
    case Intrinsic::ctpop:
    case Intrinsic::ctlz:
    case Intrinsic::cttz:
      // Non intrinsics are fine.
    case Intrinsic::not_intrinsic:
      return IRInstructionMapType::Valid;
    default:
      return IRInstructionMapType::Invalid;
    }
    return IRInstructionMapType::Valid;
  }

  // We don't take allocas from the parent function.
  // PHINodes don't cost anything and will simply become inputs.
  // Terminators will exist in both so there is no benefit from outlining
  // them.
  if (isa<AllocaInst>(I) || isa<PHINode>(I) || isa<TerminatorInst>(I))
    return IRInstructionMapType::Invalid;
  // Don't take any exception handling instructions.
  if (I->isEHPad())
    return IRInstructionMapType::Invalid;
  return IRInstructionMapType::Valid;
}

std::vector<unsigned>
llvm::mapIRModule(OutlinerMapper &OM, Module &M, ProfileSummaryInfo *PSI,
                  function_ref<BlockFrequencyInfo &(Function &)> GetBFI) {
  bool HasProfileData = PSI->hasProfileSummary();
  std::vector<unsigned> CCVec;
  unsigned CCID = 1, IllegalID = UINT_MAX;

  // Memory management for the GVN expressions used for congruency.
  SpecificBumpPtrAllocator<RelaxedExpression> ExpressionAllocator;

  // Mapping of expression to congruency id.
  using GlobalCongruencyMapTy =
      std::array<DenseMap<const RelaxedExpression *, unsigned>,
                 Instruction::OtherOpsEnd>;
  GlobalCongruencyMapTy GlobalCC;

  // Insert illegal ID at the front to act as a sentinel.
  OM.mapInstr(nullptr);
  CCVec.push_back(IllegalID--);

  bool LastWasInvalid = true;
  for (Function &F : M) {
    // Don't allow non exact definitions.
    if (!F.hasExactDefinition())
      if (!AllowODR || (!F.hasLinkOnceODRLinkage() && !F.hasWeakODRLinkage()))
        continue;
    // Be conservative about unknown GC types.
    if (F.hasGC())
      continue;
    // Don't consider dead or optnone.
    if (F.hasFnAttribute(Attribute::OptimizeNone) || F.isDefTriviallyDead())
      continue;

    // Don't outline non -Oz functions without profile data.
    bool FavorSize = F.optForMinSize();
    if (!FavorSize && !HasProfileData)
      continue;
    BlockFrequencyInfo *BFI = HasProfileData ? &GetBFI(F) : nullptr;
    for (BasicBlock &BB : F) {
      // Skip hot blocks if we have profile data.
      if (HasProfileData)
        if (FavorSize ? PSI->isHotBB(&BB, BFI) : !PSI->isColdBB(&BB, BFI))
          continue;

      // Helper for adding an invalid instruction.
      auto EmitInvalidInst = [&]() {
        LastWasInvalid = true;
        OM.mapInstr(nullptr);
        CCVec.push_back(IllegalID--);
      };

      // Try to map each instruction to a congruency id.
      for (Instruction &I : BB) {
        switch (getInstrMapType(&I)) {
          // Skip invalid/ignored instructions.
        case IRInstructionMapType::Invalid:
          if (!LastWasInvalid)
            EmitInvalidInst();
          LLVM_FALLTHROUGH;
        case IRInstructionMapType::Ignored:
          continue;
        case IRInstructionMapType::Valid:
          break;
        }
        OM.mapInstr(&I);

        // We map each valid instruction to a Relaxed expression and use
        // this for detecting congruency.
        RelaxedExpression *E =
            new (ExpressionAllocator.Allocate()) RelaxedExpression(I);
        auto ItPair = GlobalCC[I.getOpcode()].try_emplace(E, CCID);
        if (ItPair.second)
          ++CCID;
        // Use the mapped congruency ID.
        CCVec.push_back(ItPair.first->second);
        LastWasInvalid = false;

        // We need a barrier after a valid terminator.
        if (isa<InvokeInst>(&I))
          EmitInvalidInst();
      }
    }
  }

  // Dump the mapped congruencies found for the module M.
  if (DumpCC) {
#ifndef NDEBUG
    for (Function &F : M) {
      dbgs() << "function : " << F.getName() << "\n";
      for (auto &BB : F) {
        dbgs() << "block : " << BB.getName() << "\n";
        for (Instruction &I : BB) {
          unsigned Idx = OM.getInstrIdx(&I);
          unsigned CCID = Idx == unsigned(-1) ? -1 : CCVec[Idx];
          dbgs() << "-- " << CCID << " : " << I << '\n';
        }
      }
    }
    for (auto &CCIt : GlobalCC) {
      for (auto CC : CCIt) {
        size_t Idx = CC.second;
        dbgs() << "-- Examining CC ID : " << Idx << "\n";
        for (size_t i = 0, e = CCVec.size(); i < e; ++i)
          if (CCVec[i] == Idx)
            dbgs() << " - " << *OM.getInstr<Instruction>(i) << "\n";
        dbgs() << "\n";
      }
    }
#endif
  }

  // We regroup the illegal indices so that our alphabet is of a defined size.
  unsigned Diff = (UINT_MAX - IllegalID);
  for (unsigned &InstId : CCVec)
    if (InstId > IllegalID)
      InstId = 1 + (UINT_MAX - InstId);
    else
      InstId += Diff;
  return CCVec;
}
