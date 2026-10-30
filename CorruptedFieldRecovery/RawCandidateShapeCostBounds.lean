import CorruptedFieldRecovery.RawCandidateShapeCost
import CorruptedFieldRecovery.RawCandidateVerifierCost

/-! Upper envelopes for the short-circuit structural gate, including both
successful and failed branches. -/

namespace CorruptedFieldRecovery

/-- Charge for every possible shape-gate stage. The actual short-circuit
charge is bounded by this envelope regardless of where a candidate fails. -/
def rawFieldCandidateShapeWorstCaseCharge {s : Nat}
    (candidate : RawFieldCandidate s) : Nat :=
  rawShapeCompareCharge 1 s +
  rawShapeCompareCharge candidate.modulus.size (s + 1) +
  (rawFieldBitsToNatBitCosted candidate.modulus).2 + s +
  rawShapeDivisionCharge (rawFieldBitsToNat candidate.modulus) (2 ^ s) +
  rawShapeDivisionCharge (rawFieldBitsToNat candidate.modulus / 2 ^ s) 2 +
  rawShapeCompareCharge (rawFieldBitsToNat candidate.modulus / 2 ^ s % 2) 1 +
  rawShapeCompareCharge candidate.scalar.size s +
  (rawFieldBitsToNatBitCosted candidate.scalar).2 +
  rawNatBitWidth (rawFieldBitsToNat candidate.scalar)

theorem rawFieldCandidateShapeCheckBitCosted_cost_le_worst {s : Nat}
    (candidate : RawFieldCandidate s) :
    (rawFieldCandidateShapeCheckBitCosted candidate).2 ≤
      rawFieldCandidateShapeWorstCaseCharge candidate := by
  by_cases hs : 1 ≤ s
  · by_cases hm : candidate.modulus.size = s + 1
    · by_cases ht :
        rawFieldBitsToNat candidate.modulus / 2 ^ s % 2 = 1
      · by_cases hscalarSize : candidate.scalar.size = s
        · simp [rawFieldCandidateShapeCheckBitCosted,
            rawFieldCandidateShapeWorstCaseCharge, hs, hm, ht, hscalarSize,
            rawFieldBitsToNatBitCosted_fst]; omega
        · simp [rawFieldCandidateShapeCheckBitCosted,
            rawFieldCandidateShapeWorstCaseCharge, hs, hm, ht, hscalarSize,
            rawFieldBitsToNatBitCosted_fst]; omega
      · simp [rawFieldCandidateShapeCheckBitCosted,
          rawFieldCandidateShapeWorstCaseCharge, hs, hm, ht,
          rawFieldBitsToNatBitCosted_fst]; omega
    · simp [rawFieldCandidateShapeCheckBitCosted,
        rawFieldCandidateShapeWorstCaseCharge, hs, hm]; omega
  · simp [rawFieldCandidateShapeCheckBitCosted,
      rawFieldCandidateShapeWorstCaseCharge, hs]; omega

end CorruptedFieldRecovery
