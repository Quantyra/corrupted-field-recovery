import CorruptedFieldRecovery.RawRabinGcdCorrectness

/-! Quotient-class correctness for the executable repeated-squaring loop. -/

namespace CorruptedFieldRecovery

open Polynomial AdjoinRoot

/-- Every iteration of the Nat-mask Frobenius loop is an actual square in the
polynomial quotient; `rawPolynomialRemainder` supplies the representative. -/
theorem rawCandidateFrobeniusAux_quotient_sound (modulus d x : Nat)
    (hmodulus : modulus ≠ 0) :
    AdjoinRoot.mk (rawMaskPolynomial modulus)
        (rawMaskPolynomial (rawCandidateFrobeniusAux modulus d x)) =
      AdjoinRoot.mk (rawMaskPolynomial modulus)
        (rawMaskPolynomial x ^ (2 ^ d)) := by
  induction d generalizing x with
  | zero => simp [rawCandidateFrobeniusAux]
  | succ d ih =>
      simp only [rawCandidateFrobeniusAux]
      let rem := rawPolynomialRemainder (rawPolyMul x x) modulus
      have hrem := rawPolynomialRemainder_quotient_sound
        (a := rawPolyMul x x) (b := modulus) hmodulus
      have hmul : AdjoinRoot.mk (rawMaskPolynomial modulus)
          (rawMaskPolynomial (rawPolyMul x x)) =
        (AdjoinRoot.mk (rawMaskPolynomial modulus) (rawMaskPolynomial x)) ^ 2 := by
        simpa [map_mul, pow_two] using congrArg (AdjoinRoot.mk (rawMaskPolynomial modulus))
          (rawPolyMul_polynomial x x)
      have hstep : AdjoinRoot.mk (rawMaskPolynomial modulus) (rawMaskPolynomial rem) =
          (AdjoinRoot.mk (rawMaskPolynomial modulus) (rawMaskPolynomial x)) ^ 2 := by
        exact hrem.trans hmul
      calc
        AdjoinRoot.mk (rawMaskPolynomial modulus)
            (rawMaskPolynomial (rawCandidateFrobeniusAux modulus d rem)) =
            (AdjoinRoot.mk (rawMaskPolynomial modulus) (rawMaskPolynomial rem)) ^ (2 ^ d) :=
              ih rem
        _ = ((AdjoinRoot.mk (rawMaskPolynomial modulus) (rawMaskPolynomial x)) ^ 2) ^ (2 ^ d) :=
          congrArg (fun z : AdjoinRoot (rawMaskPolynomial modulus) => z ^ (2 ^ d)) hstep
        _ = (AdjoinRoot.mk (rawMaskPolynomial modulus) (rawMaskPolynomial x)) ^ (2 ^ (d + 1)) := by
          rw [← pow_mul, pow_succ]
          congr 1
          ring
        _ = AdjoinRoot.mk (rawMaskPolynomial modulus)
            (rawMaskPolynomial x ^ (2 ^ (d + 1))) := by simp [map_pow]

/-- The candidate Frobenius mask is the expected power of `X` in the
quotient by the candidate modulus. -/
theorem rawCandidateFrobenius_quotient_sound {s : Nat}
    (candidate : RawFieldCandidate s) (d : Nat)
    (hmodulus : rawFieldBitsToNat candidate.modulus ≠ 0) :
    AdjoinRoot.mk (rawCandidateModulus candidate)
        (rawMaskPolynomial (rawCandidateFrobenius candidate d)) =
      AdjoinRoot.mk (rawCandidateModulus candidate) (X ^ (2 ^ d)) := by
  change AdjoinRoot.mk (rawMaskPolynomial (rawFieldBitsToNat candidate.modulus))
      (rawMaskPolynomial (rawCandidateFrobeniusAux
        (rawFieldBitsToNat candidate.modulus) d 2)) =
    AdjoinRoot.mk (rawMaskPolynomial (rawFieldBitsToNat candidate.modulus))
      (X ^ (2 ^ d))
  have h := rawCandidateFrobeniusAux_quotient_sound
    (rawFieldBitsToNat candidate.modulus) d 2 hmodulus
  have h1 : rawMaskPolynomial 1 = (1 : Polynomial (ZMod 2)) := by
    rw [rawMaskPolynomial_step]
    norm_num [rawMaskPolynomial_zero]
  have hX : rawMaskPolynomial 2 = (X : Polynomial (ZMod 2)) := by
    rw [rawMaskPolynomial_step]
    norm_num [Nat.bodd, Nat.div2, rawMaskPolynomial_zero, h1]
  simpa [hX] using h

end CorruptedFieldRecovery
