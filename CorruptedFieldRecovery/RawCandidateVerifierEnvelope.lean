import CorruptedFieldRecovery.RawCandidateVerifierCost
import CorruptedFieldRecovery.RawCandidateShapePolynomialBound

/-! Unconditional cost envelope for the complete hfield-free fast gate,
including candidates rejected by the structural checks. -/

namespace CorruptedFieldRecovery

/-- The full instrumented verifier always pays at most the executed shape
charge, plus the range and scan envelope. When the shape gate fails, those
later stages are skipped. -/
theorem rawFieldCandidateFastCheckFullBitCosted_cost_le_all {s : Nat}
    (candidate : RawFieldCandidate s) :
    (rawFieldCandidateFastCheckFullBitCosted candidate).2 ≤
      (rawFieldCandidateShapeCheckBitCosted candidate).2 + (s / 2) ^ 2 +
        (s / 2) * rawRabinScanUniformCharge (s + 1) (s / 2) := by
  by_cases hshape : (rawFieldCandidateShapeCheckBitCosted candidate).1 = true
  · have hvalid : rawFieldCandidateShapeCheck candidate = true := by
      rw [← rawFieldCandidateShapeCheckBitCosted_fst]
      exact hshape
    exact rawFieldCandidateFastCheckFullBitCosted_cost_le candidate hvalid
  · have hfalse : (rawFieldCandidateShapeCheckBitCosted candidate).1 = false := by
      cases h : (rawFieldCandidateShapeCheckBitCosted candidate).1 <;> simp_all
    simp [rawFieldCandidateFastCheckFullBitCosted, hfalse]
    omega

/-- Combining the unconditional shape polynomial with range construction and
short-circuit scan charges gives a verifier bound valid on every candidate.
The remaining scan term is the explicit polynomial expression displayed. -/
theorem rawFieldCandidateFastCheckFullBitCosted_polynomial_envelope {s : Nat}
    (candidate : RawFieldCandidate s) :
    (rawFieldCandidateFastCheckFullBitCosted candidate).2 ≤
      100 * (s + candidate.modulus.size + candidate.scalar.size + 4) ^ 2 +
        (s / 2) ^ 2 +
        (s / 2) * rawRabinScanUniformCharge (s + 1) (s / 2) := by
  calc
    _ ≤ (rawFieldCandidateShapeCheckBitCosted candidate).2 +
        (s / 2) ^ 2 +
        (s / 2) * rawRabinScanUniformCharge (s + 1) (s / 2) :=
          rawFieldCandidateFastCheckFullBitCosted_cost_le_all candidate
    _ ≤ 100 * (s + candidate.modulus.size + candidate.scalar.size + 4) ^ 2 +
        (s / 2) ^ 2 +
        (s / 2) * rawRabinScanUniformCharge (s + 1) (s / 2) := by
          exact Nat.add_le_add_right
            (Nat.add_le_add_right
              (rawFieldCandidateShapeCheckBitCosted_polynomial_bound candidate)
              ((s / 2) ^ 2)) _

end CorruptedFieldRecovery
