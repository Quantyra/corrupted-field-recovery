import CorruptedFieldRecovery.S010ProperDegreeArithmetic
import CorruptedFieldRecovery.S010SizeArithmetic
import CorruptedFieldRecovery.ProperSubfieldCounts
import Mathlib.Tactic

namespace CorruptedFieldRecovery

/-- Specialize the half-degree geometric estimate to the exact sum used by
the accepted proper-subfield cardinality theorem, then apply s≥2R+5. -/
theorem actual_proper_degree_scaled_bound
    (K : Type*) [Field K] [Finite K] [Algebra BinaryField K]
    [FiniteDimensional BinaryField K] (s R : Nat)
    (hsdim : Module.finrank BinaryField K = s)
    (hsize : 2 * R + 5 ≤ s) :
    4 * (2 ^ R * (∑ d ∈ properDegrees K, 2 ^ d)) < 2 ^ s := by
  apply scaled_tau_lt_field_size hsize
  exact proper_degree_sum_lt_half_power K s hsdim

/-- The actual union-bound loss for nongenerators and translated-support
scalars is at most three quarters of the field. This is stronger than the
one-quarter good-fraction target, and uses the actual proper-degree sum. -/
theorem actual_scalar_bad_count_le_three_quarters
    (K : Type*) [Field K] [Finite K] [Algebra BinaryField K]
    [FiniteDimensional BinaryField K] (s R r : Nat)
    (hsdim : Module.finrank BinaryField K = s)
    (hr : r ≤ R) (hsize : 2 * R + 5 ≤ s) :
    4 * ((∑ d ∈ properDegrees K, 2 ^ d) + (2 ^ (2 * r) - 1)) ≤
      3 * 2 ^ s := by
  let T := ∑ d ∈ properDegrees K, 2 ^ d
  let B := 2 ^ (2 * r) - 1
  have hT := actual_proper_degree_scaled_bound K s R hsdim hsize
  have hpowR : 1 ≤ 2 ^ R := Nat.one_le_pow R 2 (by decide : 0 < 2)
  have hT4 : 4 * T ≤ 2 ^ s := by
    have hmul : 4 * T ≤ 4 * (2 ^ R * T) := by
      calc
        4 * T = 4 * (1 * T) := by simp
        _ ≤ 4 * (2 ^ R * T) := Nat.mul_le_mul_left 4 (Nat.mul_le_mul_right T hpowR)
    dsimp [T] at hmul hT ⊢
    omega
  have hB32 : 32 * B ≤ 2 ^ s := by
    have hsupp := scaled_support_lt_field_size hsize
    have hexp : 2 * r ≤ 2 * R := by omega
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hexp
    have hb : 2 ^ (2 * r) - 1 ≤ 2 ^ (2 * R) := (Nat.sub_le _ _).trans hp
    dsimp [B]
    exact (Nat.mul_le_mul_left 32 hb).trans hsupp
  have hB4 : 4 * B ≤ 2 ^ s := by
    have hsmall : 4 * B ≤ 32 * B := Nat.mul_le_mul_right B (by decide)
    exact hsmall.trans hB32
  have hcombine : 4 * (T + B) ≤ 3 * 2 ^ s := by omega
  simpa [T, B] using hcombine

/-- The finite complement count appearing in `card_goodFiveTupleSigma_lower`
is at least one quarter of all field scalars. -/
theorem actual_good_scalar_finite_count_lower
    (K : Type*) [Field K] [Finite K] [Algebra BinaryField K]
    [FiniteDimensional BinaryField K] (s R r : Nat)
    (hsdim : Module.finrank BinaryField K = s)
    (hr : r ≤ R) (hsize : 2 * R + 5 ≤ s) :
    4 * (2 ^ s -
      ((∑ d ∈ properDegrees K, 2 ^ d) + (2 ^ (2 * r) - 1))) ≥ 2 ^ s := by
  have hbad := actual_scalar_bad_count_le_three_quarters K s R r hsdim hr hsize
  have hle : (∑ d ∈ properDegrees K, 2 ^ d) + (2 ^ (2 * r) - 1) ≤ 2 ^ s := by
    omega
  omega
end CorruptedFieldRecovery