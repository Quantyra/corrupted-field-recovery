import CorruptedFieldRecovery.RawRabinCoprimeResidue

/-! Semantic meaning of every individual executable Rabin gcd test and of
the complete finite scan. -/

namespace CorruptedFieldRecovery

open Polynomial AdjoinRoot

/-- The hfield-free Boolean scan is true exactly when the candidate modulus is
coprime to every standard binary Frobenius polynomial in the tested range. -/
theorem rawCandidateRabinCheck_eq_true_iff_frobenius_coprime {s : Nat}
    (candidate : RawFieldCandidate s)
    (hmodulus : rawFieldBitsToNat candidate.modulus ≠ 0) :
    rawCandidateRabinCheck candidate = true ↔
      ∀ d, 1 ≤ d → d ≤ s / 2 →
        rawMaskPairCoprime (rawFieldBitsToNat candidate.modulus)
          (rawBitsToNat (rawPolynomialBits (X ^ (2 ^ d) - X))) := by
  rw [rawCandidateRabinCheck_eq_true_iff]
  constructor
  · intro h d hdlo hdhi
    have hgcd := h d hdlo hdhi
    have hcop := (rawPolynomialGcd_one_iff_coprime
      (rawFieldBitsToNat candidate.modulus)
      (Nat.xor (rawCandidateFrobenius candidate d) 2)).mp hgcd
    let targetMask := rawBitsToNat (rawPolynomialBits (X ^ (2 ^ d) - X))
    have hdecode : rawMaskPolynomial targetMask = X ^ (2 ^ d) - X :=
      rawPolynomialBits_mask_decode _
    have hoperand := rawCandidateRabinOperand_quotient_sound candidate d hmodulus
    change AdjoinRoot.mk (rawMaskPolynomial (rawFieldBitsToNat candidate.modulus))
        (rawMaskPolynomial (Nat.xor (rawCandidateFrobenius candidate d) 2)) =
      AdjoinRoot.mk (rawMaskPolynomial (rawFieldBitsToNat candidate.modulus))
        (X ^ (2 ^ d) - X) at hoperand
    have hquot : AdjoinRoot.mk (rawMaskPolynomial (rawFieldBitsToNat candidate.modulus))
        (rawMaskPolynomial (Nat.xor (rawCandidateFrobenius candidate d) 2)) =
      AdjoinRoot.mk (rawMaskPolynomial (rawFieldBitsToNat candidate.modulus))
        (rawMaskPolynomial targetMask) := by
      calc
        _ = AdjoinRoot.mk (rawMaskPolynomial (rawFieldBitsToNat candidate.modulus))
            (X ^ (2 ^ d) - X) := hoperand
        _ = AdjoinRoot.mk (rawMaskPolynomial (rawFieldBitsToNat candidate.modulus))
            (rawMaskPolynomial targetMask) := by
              exact congrArg (AdjoinRoot.mk
                (rawMaskPolynomial (rawFieldBitsToNat candidate.modulus))) hdecode.symm
    change rawMaskPairCoprime (rawFieldBitsToNat candidate.modulus) targetMask
    exact (rawMaskPairCoprime_quotient_congruent
      (rawFieldBitsToNat candidate.modulus)
      (Nat.xor (rawCandidateFrobenius candidate d) 2) targetMask hquot).mp hcop
  · intro h d hdlo hdhi
    have hgcdcop := h d hdlo hdhi
    let targetMask := rawBitsToNat (rawPolynomialBits (X ^ (2 ^ d) - X))
    have hdecode : rawMaskPolynomial targetMask = X ^ (2 ^ d) - X :=
      rawPolynomialBits_mask_decode _
    have hoperand := rawCandidateRabinOperand_quotient_sound candidate d hmodulus
    change AdjoinRoot.mk (rawMaskPolynomial (rawFieldBitsToNat candidate.modulus))
        (rawMaskPolynomial (Nat.xor (rawCandidateFrobenius candidate d) 2)) =
      AdjoinRoot.mk (rawMaskPolynomial (rawFieldBitsToNat candidate.modulus))
        (X ^ (2 ^ d) - X) at hoperand
    have hquot : AdjoinRoot.mk (rawMaskPolynomial (rawFieldBitsToNat candidate.modulus))
        (rawMaskPolynomial (Nat.xor (rawCandidateFrobenius candidate d) 2)) =
      AdjoinRoot.mk (rawMaskPolynomial (rawFieldBitsToNat candidate.modulus))
        (rawMaskPolynomial targetMask) := by
      calc
        _ = AdjoinRoot.mk (rawMaskPolynomial (rawFieldBitsToNat candidate.modulus))
            (X ^ (2 ^ d) - X) := hoperand
        _ = AdjoinRoot.mk (rawMaskPolynomial (rawFieldBitsToNat candidate.modulus))
            (rawMaskPolynomial targetMask) := by
              exact congrArg (AdjoinRoot.mk
                (rawMaskPolynomial (rawFieldBitsToNat candidate.modulus))) hdecode.symm
    have hcopxor := (rawMaskPairCoprime_quotient_congruent
      (rawFieldBitsToNat candidate.modulus)
      (Nat.xor (rawCandidateFrobenius candidate d) 2) targetMask hquot).mpr hgcdcop
    exact (rawPolynomialGcd_one_iff_coprime
      (rawFieldBitsToNat candidate.modulus)
      (Nat.xor (rawCandidateFrobenius candidate d) 2)).mpr hcopxor

end CorruptedFieldRecovery
