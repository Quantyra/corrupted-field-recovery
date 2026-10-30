import CorruptedFieldRecovery.RawRabinIrreducibleCriterion
import CorruptedFieldRecovery.RawRabinScanCoprime
import CorruptedFieldRecovery.RawPolynomialIrreducibility

/-! Connect the executable Rabin candidate gate to the existing mathematical
candidate predicate, without using the legacy exhaustive predicate as a
premise. -/

namespace CorruptedFieldRecovery

open Polynomial

theorem rawFieldCandidateShapeCheck_iff {s : Nat}
    (candidate : RawFieldCandidate s) :
    rawFieldCandidateShapeCheck candidate = true ↔
      1 ≤ s ∧ candidate.modulus.size = s + 1 ∧
      rawFieldBitsToNat candidate.modulus / 2 ^ s % 2 = 1 ∧
      candidate.scalar.size = s ∧ rawFieldBitsToNat candidate.scalar ≠ 0 := by
  simp [rawFieldCandidateShapeCheck, and_assoc]

/-- The shape gate alone proves the modulus is monic of the claimed degree. -/
theorem rawFieldCandidateShapeCheck_modulus_polynomial {s : Nat}
    (candidate : RawFieldCandidate s)
    (hshape : rawFieldCandidateShapeCheck candidate = true) :
    (rawMaskPolynomial (rawFieldBitsToNat candidate.modulus)).Monic ∧
      (rawMaskPolynomial (rawFieldBitsToNat candidate.modulus)).natDegree = s := by
  rcases (rawFieldCandidateShapeCheck_iff candidate).mp hshape with
    ⟨hs, hsize, htop, _, _⟩
  have hlen : candidate.modulus.toList.length = s + 1 := by
    simpa using hsize
  obtain ⟨preBits, hbits, hprelen⟩ := rawBitsToNat_lastBit_of_top
    candidate.modulus.toList s hlen htop
  have hpre0 : preBits ≠ [] := by
    intro he
    simp [he] at hprelen
    omega
  have hpredegree : (rawBoolListPolynomial preBits).natDegree < s := by
    rw [← hprelen]
    exact rawBoolListPolynomial_natDegree_lt_length preBits hpre0
  have hlistDegree : IsMonicOfDegree
      (rawBoolListPolynomial candidate.modulus.toList) s := by
    rw [hbits, rawBoolListPolynomial_append, hprelen]
    simpa [rawBoolListPolynomial] using
      (isMonicOfDegree_X_pow (ZMod 2) s).add_left hpredegree
  have harrayMonic : (rawFieldArrayPolynomial candidate.modulus).Monic := by
    simpa [rawFieldArrayPolynomial] using hlistDegree.monic
  have harrayDegree : (rawFieldArrayPolynomial candidate.modulus).natDegree = s := by
    simpa [rawFieldArrayPolynomial] using hlistDegree.natDegree_eq
  rw [rawFieldArrayPolynomial_eq_mask] at harrayMonic harrayDegree
  exact ⟨harrayMonic, harrayDegree⟩

theorem rawCandidateRabinCheck_eq_true_iff_irreducible {s : Nat}
    (candidate : RawFieldCandidate s)
    (hshape : rawFieldCandidateShapeCheck candidate = true) :
    rawCandidateRabinCheck candidate = true ↔
      Irreducible (rawMaskPolynomial (rawFieldBitsToNat candidate.modulus)) := by
  have hstructure := rawFieldCandidateShapeCheck_iff candidate |>.mp hshape
  rcases hstructure with ⟨hs, _, _, _, _⟩
  have hmod := rawFieldCandidateShapeCheck_modulus_polynomial candidate hshape
  have hmaskne : rawFieldBitsToNat candidate.modulus ≠ 0 := by
    intro hz
    apply hmod.1.ne_zero
    rw [hz, rawMaskPolynomial_zero]
  have hscan := rawCandidateRabinCheck_eq_true_iff_frobenius_coprime
    candidate hmaskne
  have hcriterion := monic_irreducible_iff_frobenius_coprime
    hmod.1 s hmod.2 hs
  have hscanPolynomial : rawCandidateRabinCheck candidate = true ↔
      ∀ d, 1 ≤ d → d ≤ s / 2 →
        rawPolynomialCoprime
          (rawMaskPolynomial (rawFieldBitsToNat candidate.modulus))
          (X ^ (2 ^ d) - X) := by
    rw [hscan]
    constructor
    · intro h d hdlo hdhi
      have hp := h d hdlo hdhi
      change ∀ c : Polynomial (ZMod 2),
        c ∣ rawMaskPolynomial (rawFieldBitsToNat candidate.modulus) →
        c ∣ rawMaskPolynomial
          (rawBitsToNat (rawPolynomialBits (X ^ (2 ^ d) - X))) → IsUnit c at hp
      intro c hcf hcx
      have hcx' : c ∣ rawMaskPolynomial
          (rawBitsToNat (rawPolynomialBits (X ^ (2 ^ d) - X))) := by
        rw [rawPolynomialBits_mask_decode]
        exact hcx
      exact hp c hcf hcx'
    · intro h d hdlo hdhi
      have hp := h d hdlo hdhi
      let mask := rawBitsToNat (rawPolynomialBits (X ^ (2 ^ d) - X))
      have hdecode : rawMaskPolynomial mask = X ^ (2 ^ d) - X :=
        rawPolynomialBits_mask_decode _
      change ∀ c : Polynomial (ZMod 2),
        c ∣ rawMaskPolynomial (rawFieldBitsToNat candidate.modulus) →
        c ∣ rawMaskPolynomial mask → IsUnit c
      intro c hcf hcm
      have hcm' : c ∣ X ^ (2 ^ d) - X := by
        rw [← hdecode]
        exact hcm
      exact hp c hcf hcm'
  exact hscanPolynomial.trans hcriterion.symm

/-- The fast executable gate is extensionally equivalent to the legacy
mathematical validity predicate, while using only shape checks and the Rabin
scan at runtime. -/
theorem rawFieldCandidateFastCheck_eq_true_iff_valid {s : Nat}
    (candidate : RawFieldCandidate s) :
    rawFieldCandidateFastCheck candidate = true ↔ rawFieldCandidateValid candidate := by
  constructor
  · intro hfast
    simp only [rawFieldCandidateFastCheck, Bool.and_eq_true] at hfast
    rcases hfast with ⟨hshape, hrabin⟩
    rcases (rawFieldCandidateShapeCheck_iff candidate).mp hshape with
      ⟨hs, hsize, htop, hscalarSize, hscalar⟩
    have hmod := rawFieldCandidateShapeCheck_modulus_polynomial candidate hshape
    have hirr := (rawCandidateRabinCheck_eq_true_iff_irreducible candidate hshape).mp hrabin
    have hraw := polynomial_irreducible_implies_rawIrreducible_mask
      (rawFieldBitsToNat candidate.modulus) s hs hmod.2 hmod.1 hirr
    exact ⟨hs, hsize, htop, hscalarSize, hscalar, hraw⟩
  · intro hvalid
    have hvalidOriginal := hvalid
    rcases hvalid with ⟨hs, hsize, htop, hscalarSize, hscalar, hraw⟩
    have hshape : rawFieldCandidateShapeCheck candidate = true := by
      apply (rawFieldCandidateShapeCheck_iff candidate).mpr
      exact ⟨hs, hsize, htop, hscalarSize, hscalar⟩
    have hmod := rawFieldCandidateValid_modulus_polynomial candidate hvalidOriginal
    have hirr := rawIrreducible_mask_implies_polynomial_irreducible
      (rawFieldBitsToNat candidate.modulus) s hs hmod.2 hmod.1 hraw
    have hrabin := (rawCandidateRabinCheck_eq_true_iff_irreducible candidate hshape).mpr hirr
    simp [rawFieldCandidateFastCheck, hshape, hrabin]

end CorruptedFieldRecovery
