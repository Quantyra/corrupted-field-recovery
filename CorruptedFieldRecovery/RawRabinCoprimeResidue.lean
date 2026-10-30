import CorruptedFieldRecovery.RawRabinScan

/-! Relate the actual XOR-mask gcd operand to the standard Frobenius
polynomial using quotient congruence. -/

namespace CorruptedFieldRecovery

open Polynomial AdjoinRoot

/-- Common-divisor coprimality with a fixed mask is invariant when the second
polynomial is replaced by a quotient-congruent representative. -/
theorem rawMaskPairCoprime_quotient_congruent
    (modulus a b : Nat)
    (hcong : AdjoinRoot.mk (rawMaskPolynomial modulus) (rawMaskPolynomial a) =
      AdjoinRoot.mk (rawMaskPolynomial modulus) (rawMaskPolynomial b)) :
    rawMaskPairCoprime modulus a ↔ rawMaskPairCoprime modulus b := by
  have hdiv : rawMaskPolynomial modulus ∣
      rawMaskPolynomial b - rawMaskPolynomial a :=
    AdjoinRoot.mk_eq_mk.mp hcong.symm
  constructor
  · intro ha c hcm hca
    have hdiff : c ∣ rawMaskPolynomial b - rawMaskPolynomial a := hcm.trans hdiv
    have hcb : c ∣ rawMaskPolynomial a := by
      have hsub : rawMaskPolynomial a =
          rawMaskPolynomial b - (rawMaskPolynomial b - rawMaskPolynomial a) := by ring
      rw [hsub]
      exact dvd_sub hca hdiff
    exact ha c hcm hcb
  · intro hb c hcm hcb
    have hdiff : c ∣ rawMaskPolynomial b - rawMaskPolynomial a := hcm.trans hdiv
    have hca : c ∣ rawMaskPolynomial b := by
      have hadd : rawMaskPolynomial b =
          (rawMaskPolynomial b - rawMaskPolynomial a) + rawMaskPolynomial a := by ring
      rw [hadd]
      exact dvd_add hdiff hcb
    exact hb c hcm hca

/-- The executable XOR operand represents `X^(2^d)-X` in the quotient by
the candidate modulus. This uses the proved raw Frobenius and XOR refinements. -/
theorem rawCandidateRabinOperand_quotient_sound {s : Nat}
    (candidate : RawFieldCandidate s) (d : Nat)
    (hmodulus : rawFieldBitsToNat candidate.modulus ≠ 0) :
    AdjoinRoot.mk (rawCandidateModulus candidate)
      (rawMaskPolynomial
        (Nat.xor (rawCandidateFrobenius candidate d) 2)) =
    AdjoinRoot.mk (rawCandidateModulus candidate) (X ^ (2 ^ d) - X) := by
  change AdjoinRoot.mk (rawMaskPolynomial (rawFieldBitsToNat candidate.modulus))
      (rawMaskPolynomial (Nat.xor (rawCandidateFrobenius candidate d) 2)) =
    AdjoinRoot.mk (rawMaskPolynomial (rawFieldBitsToNat candidate.modulus))
      (X ^ (2 ^ d) - X)
  have h1 : rawMaskPolynomial 1 = (1 : Polynomial (ZMod 2)) := by
    rw [rawMaskPolynomial_step]
    norm_num [rawMaskPolynomial_zero]
  have hX : rawMaskPolynomial 2 = (X : Polynomial (ZMod 2)) := by
    rw [rawMaskPolynomial_step]
    norm_num [Nat.bodd, Nat.div2, rawMaskPolynomial_zero, h1]
  have hxor : rawMaskPolynomial (Nat.xor (rawCandidateFrobenius candidate d) 2) =
      rawMaskPolynomial (rawCandidateFrobenius candidate d) + X := by
    rw [rawMaskPolynomial_xor, hX]
  have hFrob := rawCandidateFrobenius_quotient_sound candidate d hmodulus
  change AdjoinRoot.mk (rawMaskPolynomial (rawFieldBitsToNat candidate.modulus))
      (rawMaskPolynomial (rawCandidateFrobenius candidate d)) =
    AdjoinRoot.mk (rawMaskPolynomial (rawFieldBitsToNat candidate.modulus))
      (X ^ (2 ^ d)) at hFrob
  calc
    AdjoinRoot.mk (rawMaskPolynomial (rawFieldBitsToNat candidate.modulus))
        (rawMaskPolynomial (Nat.xor (rawCandidateFrobenius candidate d) 2)) =
      AdjoinRoot.mk (rawMaskPolynomial (rawFieldBitsToNat candidate.modulus))
        (rawMaskPolynomial (rawCandidateFrobenius candidate d) + X) :=
          congrArg (AdjoinRoot.mk (rawMaskPolynomial (rawFieldBitsToNat candidate.modulus))) hxor
    _ = AdjoinRoot.mk (rawMaskPolynomial (rawFieldBitsToNat candidate.modulus))
          (rawMaskPolynomial (rawCandidateFrobenius candidate d)) +
        AdjoinRoot.mk (rawMaskPolynomial (rawFieldBitsToNat candidate.modulus)) X := by
          simp [map_add]
    _ = AdjoinRoot.mk (rawMaskPolynomial (rawFieldBitsToNat candidate.modulus))
          (X ^ (2 ^ d)) +
        AdjoinRoot.mk (rawMaskPolynomial (rawFieldBitsToNat candidate.modulus)) X := by
          rw [hFrob]
    _ = AdjoinRoot.mk (rawMaskPolynomial (rawFieldBitsToNat candidate.modulus))
          (X ^ (2 ^ d) - X) := by
          have hxx : (X : Polynomial (ZMod 2)) + X = 0 := by
            ext n
            by_cases hn : n = 1
            · subst n
              simp only [coeff_add, coeff_X]
              decide
            · have hne : 1 ≠ n := by omega
              simp [coeff_add, coeff_X, hne]
          have hneg : -(X : Polynomial (ZMod 2)) = X := by
            calc
              -X = -X + 0 := by simp
              _ = -X + (X + X) := by simp [hxx]
              _ = X := by abel
          calc
            _ = AdjoinRoot.mk (rawMaskPolynomial (rawFieldBitsToNat candidate.modulus))
                (X ^ (2 ^ d) - X) := congrArg
                  (AdjoinRoot.mk (rawMaskPolynomial (rawFieldBitsToNat candidate.modulus)))
                  (by rw [sub_eq_add_neg, hneg])

end CorruptedFieldRecovery
