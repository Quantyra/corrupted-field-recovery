import CorruptedFieldRecovery.RawRabinIrreducibility

/-! Refinement lemmas connecting the Nat-mask Euclidean step to polynomial
divisibility. -/

namespace CorruptedFieldRecovery

open Polynomial AdjoinRoot

/-- Replacing a dividend by its raw polynomial remainder preserves the
common divisors with the modulus. This is the Euclidean invariant needed to
show that the Nat-mask gcd computes polynomial coprimality. -/
theorem rawPolynomialRemainder_commonDivisors {a b c : Nat} (hb : b ≠ 0) :
    (rawMaskPolynomial c ∣ rawMaskPolynomial a ∧
      rawMaskPolynomial c ∣ rawMaskPolynomial b) ↔
    (rawMaskPolynomial c ∣ rawMaskPolynomial b ∧
      rawMaskPolynomial c ∣ rawMaskPolynomial (rawPolynomialRemainder a b)) := by
  have hcong := rawPolynomialRemainder_quotient_sound (a := a) (b := b) hb
  rw [AdjoinRoot.mk_eq_mk] at hcong
  constructor
  · rintro ⟨ha, hmod⟩
    refine ⟨hmod, ?_⟩
    have hdiff : rawMaskPolynomial c ∣
        rawMaskPolynomial (rawPolynomialRemainder a b) - rawMaskPolynomial a :=
      hmod.trans hcong
    have hadd := dvd_add hdiff ha
    simpa [sub_add_cancel] using hadd
  · rintro ⟨hmod, hrem⟩
    refine ⟨?_, hmod⟩
    have hdiff : rawMaskPolynomial c ∣
        rawMaskPolynomial (rawPolynomialRemainder a b) - rawMaskPolynomial a :=
      hmod.trans hcong
    have hsub := dvd_sub hrem hdiff
    convert hsub using 1
    ring

end CorruptedFieldRecovery
