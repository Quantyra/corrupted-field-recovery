import CorruptedFieldRecovery.RawFieldQuotient

/-! Bounded Nat-mask arithmetic for quotient representatives.  Reduction is
performed directly on the serialized polynomial masks; this module does not
use `AdjoinRoot` field operations to compute an answer. -/

namespace CorruptedFieldRecovery

open Polynomial AdjoinRoot

/-- One long-division cancellation step, with low-endian polynomial masks. -/
def rawReduceStep (modulus degree a : Nat) : Nat :=
  Nat.xor a (modulus * 2 ^ (Nat.log2 a - degree))

/-- Fuel-bounded long division.  A caller chooses the fuel; semantic
correctness below holds for every fuel, including a run that stops early. -/
def rawReduceFuel (modulus degree : Nat) : Nat → Nat → Nat
  | 0, a => a
  | fuel + 1, a =>
      if a < 2 ^ degree then a
      else rawReduceFuel modulus degree fuel (rawReduceStep modulus degree a)

/-- Carryless product reduced by the serialized candidate modulus. -/
def rawFieldMulFuel {s : Nat} (candidate : RawFieldCandidate s) (fuel a b : Nat) : Nat :=
  rawReduceFuel (rawFieldBitsToNat candidate.modulus) s fuel (rawPolyMul a b)

theorem rawMaskPolynomial_mul_pow_two (a k : Nat) :
    rawMaskPolynomial (a * 2 ^ k) = rawMaskPolynomial a * X ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hmul : a * 2 ^ (k + 1) = 2 * (a * 2 ^ k) := by
        rw [pow_succ]
        ring
      rw [hmul, rawMaskPolynomial_shift, ih, pow_succ]
      ac_rfl

/-- Every reduction step preserves the polynomial's quotient class, whether
or not a caller supplies enough fuel to reach the canonical remainder. -/
theorem rawReduceStep_quotient_sound (modulus degree a : Nat) :
    AdjoinRoot.mk (rawMaskPolynomial modulus)
      (rawMaskPolynomial (rawReduceStep modulus degree a)) =
    AdjoinRoot.mk (rawMaskPolynomial modulus) (rawMaskPolynomial a) := by
  rw [AdjoinRoot.mk_eq_mk]
  rw [rawReduceStep, rawMaskPolynomial_xor, rawMaskPolynomial_mul_pow_two]
  refine ⟨X ^ (Nat.log2 a - degree), ?_⟩
  ring

/-- The bounded Nat implementation refines quotient arithmetic: the reduced
mask and the original mask denote the same class in the polynomial quotient. -/
theorem rawReduceFuel_quotient_sound (modulus degree fuel a : Nat) :
    AdjoinRoot.mk (rawMaskPolynomial modulus)
      (rawMaskPolynomial (rawReduceFuel modulus degree fuel a)) =
    AdjoinRoot.mk (rawMaskPolynomial modulus) (rawMaskPolynomial a) := by
  induction fuel generalizing a with
  | zero => rfl
  | succ fuel ih =>
      by_cases h : a < 2 ^ degree
      · simp [rawReduceFuel, h]
      · rw [rawReduceFuel, if_neg h]
        exact (ih (rawReduceStep modulus degree a)).trans
          (rawReduceStep_quotient_sound modulus degree a)

/-- The raw carryless product agrees with multiplication of the decoded
polynomial representatives. -/
theorem rawFieldMulFuel_quotient_sound {s : Nat} (candidate : RawFieldCandidate s)
    (fuel a b : Nat) :
    AdjoinRoot.mk (rawCandidateModulus candidate)
      (rawMaskPolynomial (rawFieldMulFuel candidate fuel a b)) =
    AdjoinRoot.mk (rawCandidateModulus candidate)
      (rawMaskPolynomial a * rawMaskPolynomial b) := by
  change AdjoinRoot.mk (rawMaskPolynomial (rawFieldBitsToNat candidate.modulus))
      (rawMaskPolynomial (rawReduceFuel (rawFieldBitsToNat candidate.modulus) s fuel
        (rawPolyMul a b))) =
    AdjoinRoot.mk (rawMaskPolynomial (rawFieldBitsToNat candidate.modulus))
      (rawMaskPolynomial a * rawMaskPolynomial b)
  rw [rawReduceFuel_quotient_sound]
  rw [rawPolyMul_polynomial]

end CorruptedFieldRecovery
