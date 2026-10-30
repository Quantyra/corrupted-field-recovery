import CorruptedFieldRecovery.RawRabinGcdRefinement
import CorruptedFieldRecovery.RawPolynomialIrreducibility

/-! Correctness of the Nat-mask Euclidean gcd, stated against polynomial
coprimality rather than against a second Nat implementation. -/

namespace CorruptedFieldRecovery

open Polynomial

/-- Polynomial coprimality for two decoded Nat masks, expressed by the
universal common-divisor characterization. -/
def rawMaskPairCoprime (a b : Nat) : Prop :=
  ∀ c : Polynomial (ZMod 2),
    c ∣ rawMaskPolynomial a → c ∣ rawMaskPolynomial b → IsUnit c

private theorem rawMaskPolynomial_one : rawMaskPolynomial 1 = (1 : Polynomial (ZMod 2)) := by
  rw [rawMaskPolynomial_step]
  norm_num [rawMaskPolynomial_zero]

private theorem rawMaskPolynomial_unit_iff_one (n : Nat) :
    IsUnit (rawMaskPolynomial n) ↔ n = 1 := by
  by_cases hn : n = 0
  · subst n
    simp [rawMaskPolynomial_zero]
  have hlow : 2 ^ Nat.log2 n ≤ n := Nat.log2_self_le hn
  have hupp : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
  have hmono := rawMaskPolynomial_isMonicOfDegree_of_range n (Nat.log2 n) hlow hupp
  have hdegree := hmono.natDegree_eq
  constructor
  · intro hunit
    have hzero : (rawMaskPolynomial n).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit hunit
    have hpoly : rawMaskPolynomial n = 1 :=
      hmono.monic.natDegree_eq_zero.mp (by omega)
    have hmask : rawMaskPolynomial n = rawMaskPolynomial 1 := by
      rw [rawMaskPolynomial_one]
      exact hpoly
    exact rawMaskPolynomial_injective hmask
  · intro h
    subst n
    rw [rawMaskPolynomial_one]
    exact isUnit_one

private theorem rawMaskPairCoprime_zero_iff (a : Nat) :
    rawMaskPairCoprime a 0 ↔ a = 1 := by
  constructor
  · intro h
    have hu : IsUnit (rawMaskPolynomial a) :=
      h (rawMaskPolynomial a) dvd_rfl (by rw [rawMaskPolynomial_zero]; exact dvd_zero _)
    exact rawMaskPolynomial_unit_iff_one a |>.mp hu
  · intro ha
    subst a
    intro c hc _
    rw [rawMaskPolynomial_one] at hc
    exact isUnit_of_dvd_one hc

private theorem rawMaskPairCoprime_one (a : Nat) :
    rawMaskPairCoprime a 1 := by
  intro c _ hc
  rw [rawMaskPolynomial_one] at hc
  exact isUnit_of_dvd_one hc

private theorem rawMaskRemainderCoprime_iff (a b : Nat) (hb : b ≠ 0) :
    rawMaskPairCoprime a b ↔
      rawMaskPairCoprime b (rawPolynomialRemainder a b) := by
  constructor
  · intro h c hcb hcr
    have hdecode : rawMaskPolynomial (rawBitsToNat (rawPolynomialBits c)) = c :=
      rawPolynomialBits_mask_decode c
    have hmB : rawMaskPolynomial (rawBitsToNat (rawPolynomialBits c)) ∣
        rawMaskPolynomial b := by simpa [hdecode] using hcb
    have hmR : rawMaskPolynomial (rawBitsToNat (rawPolynomialBits c)) ∣
        rawMaskPolynomial (rawPolynomialRemainder a b) := by
      simpa [hdecode] using hcr
    have hpair := (rawPolynomialRemainder_commonDivisors
      (a := a) (b := b) (c := rawBitsToNat (rawPolynomialBits c)) hb).mpr
      ⟨hmB, hmR⟩
    exact h c (by simpa [hdecode] using hpair.1)
      (by simpa [hdecode] using hpair.2)
  · intro h c hca hcb
    have hdecode : rawMaskPolynomial (rawBitsToNat (rawPolynomialBits c)) = c :=
      rawPolynomialBits_mask_decode c
    have hmA : rawMaskPolynomial (rawBitsToNat (rawPolynomialBits c)) ∣
        rawMaskPolynomial a := by simpa [hdecode] using hca
    have hmB : rawMaskPolynomial (rawBitsToNat (rawPolynomialBits c)) ∣
        rawMaskPolynomial b := by simpa [hdecode] using hcb
    have hpair := (rawPolynomialRemainder_commonDivisors
      (a := a) (b := b) (c := rawBitsToNat (rawPolynomialBits c)) hb).mp
      ⟨hmA, hmB⟩
    exact h c (by simpa [hdecode] using hpair.1)
      (by simpa [hdecode] using hpair.2)

/-- The Nat Euclidean recursion returns mask `1` exactly when the decoded
polynomials have no nonunit common divisor. The quantifier ranges over every
polynomial, using the proved complete mask encoding for each divisor. -/
theorem rawPolynomialGcd_one_iff_coprime (a b : Nat) :
    rawPolynomialGcd a b = 1 ↔ rawMaskPairCoprime a b := by
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
      cases b with
      | zero =>
          simp only [rawPolynomialGcd]
          exact (rawMaskPairCoprime_zero_iff a).symm
      | succ b =>
          cases b with
          | zero =>
              constructor
              · intro _
                exact rawMaskPairCoprime_one a
              · intro _
                change rawPolynomialGcd a 1 = 1
                rw [rawPolynomialGcd]
          | succ b =>
              let modulus := b + 2
              let rem := rawPolynomialRemainder a modulus
              have hmodulus : modulus ≠ 0 := by simp [modulus]
              have hlt : rem < modulus := by
                exact rawPolynomialRemainder_lt (a := a) (b := modulus) hmodulus
              have hrec := ih rem hlt modulus
              change (rawPolynomialGcd modulus rem = 1 ↔
                rawMaskPairCoprime modulus rem) at hrec
              rw [rawPolynomialGcd]
              change (rawPolynomialGcd modulus rem = 1 ↔
                rawMaskPairCoprime a modulus)
              exact hrec.trans (rawMaskRemainderCoprime_iff a modulus hmodulus).symm

end CorruptedFieldRecovery
