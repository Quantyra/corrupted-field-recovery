import CorruptedFieldRecovery.RawPolynomialIrreducibility
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.Finiteness

/-! Quotient-field construction and the nonzero scalar residue from an
accepted finite raw candidate. -/

namespace CorruptedFieldRecovery

noncomputable def rawCandidateModulus {s : Nat} (candidate : RawFieldCandidate s) :
    Polynomial (ZMod 2) :=
  rawMaskPolynomial (rawFieldBitsToNat candidate.modulus)

noncomputable def rawCandidateScalar {s : Nat} (candidate : RawFieldCandidate s) :
    Polynomial (ZMod 2) :=
  rawFieldArrayPolynomial candidate.scalar

theorem accepted_rawCandidateModulus_monic {s : Nat}
    (candidate : RawFieldCandidate s) (hcheck : rawFieldCandidateCheck candidate = true) :
    (rawCandidateModulus candidate).Monic := by
  have hvalid := accepted_rawFieldCandidateCheck candidate hcheck
  exact (rawFieldCandidateValid_modulus_polynomial candidate hvalid).1

theorem accepted_rawCandidateModulus_irreducible {s : Nat}
    (candidate : RawFieldCandidate s) (hcheck : rawFieldCandidateCheck candidate = true) :
    Irreducible (rawCandidateModulus candidate) := by
  simpa [rawCandidateModulus] using
    accepted_rawFieldCandidateCheck_polynomial_irreducible candidate hcheck

theorem accepted_rawCandidate_quotient_field {s : Nat}
    (candidate : RawFieldCandidate s) (hcheck : rawFieldCandidateCheck candidate = true) :
    Nonempty (Field (AdjoinRoot (rawCandidateModulus candidate))) := by
  letI : Fact (Irreducible (rawCandidateModulus candidate)) :=
    ⟨accepted_rawCandidateModulus_irreducible candidate hcheck⟩
  exact ⟨inferInstance⟩

theorem accepted_rawCandidate_quotient_card {s : Nat}
    (candidate : RawFieldCandidate s) (hcheck : rawFieldCandidateCheck candidate = true) :
    Nat.card (AdjoinRoot (rawCandidateModulus candidate)) = 2 ^ s := by
  have hvalid := accepted_rawFieldCandidateCheck candidate hcheck
  rcases hvalid with ⟨hs, hsize, htop, hscalarSize, hscalarNonzero, hirred⟩
  have hmod := rawFieldCandidateValid_modulus_polynomial candidate
    ⟨hs, hsize, htop, hscalarSize, hscalarNonzero, hirred⟩
  letI : Module.Finite (ZMod 2) (AdjoinRoot (rawCandidateModulus candidate)) := by
    simpa [rawCandidateModulus] using
      (hmod.1.finite_adjoinRoot)
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := AdjoinRoot (rawCandidateModulus candidate)),
    Module.finrank_eq_card_basis (AdjoinRoot.powerBasisAux' (by
      simpa [rawCandidateModulus] using hmod.1))]
  simp [rawCandidateModulus, hmod.2, Nat.card_eq_fintype_card, ZMod.card]

theorem accepted_rawCandidate_scalar_residue_ne_zero {s : Nat}
    (candidate : RawFieldCandidate s) (hcheck : rawFieldCandidateCheck candidate = true) :
    AdjoinRoot.mk (rawCandidateModulus candidate) (rawCandidateScalar candidate) ≠ 0 := by
  have hvalid := accepted_rawFieldCandidateCheck candidate hcheck
  rcases hvalid with ⟨hs, hmodsize, htop, hscalarsize, hscalarNonzero, hirred⟩
  have hmod := rawFieldCandidateValid_modulus_polynomial candidate
    ⟨hs, hmodsize, htop, hscalarsize, hscalarNonzero, hirred⟩
  have hscalarNonzeroPoly : rawCandidateScalar candidate ≠ 0 := by
    intro hzero
    have hmaskzero : rawMaskPolynomial (rawFieldBitsToNat candidate.scalar) = 0 := by
      rw [← rawFieldArrayPolynomial_eq_mask]
      simpa [rawCandidateScalar] using hzero
    have hmaskEq : rawMaskPolynomial (rawFieldBitsToNat candidate.scalar) =
        rawMaskPolynomial 0 := by simpa [rawMaskPolynomial_zero] using hmaskzero
    exact hscalarNonzero (rawMaskPolynomial_injective hmaskEq)
  have hscalarLength : candidate.scalar.toList.length = s := by simpa using hscalarsize
  have hscalarListNonempty : candidate.scalar.toList ≠ [] := by
    intro hnil
    simp [hnil] at hscalarLength
    omega
  have hscalarDegree : (rawCandidateScalar candidate).natDegree < s := by
    have h := rawBoolListPolynomial_natDegree_lt_length
      candidate.scalar.toList hscalarListNonempty
    rw [hscalarLength] at h
    simpa [rawCandidateScalar, rawFieldArrayPolynomial] using h
  have hdegreeLt : (rawCandidateScalar candidate).natDegree <
      (rawCandidateModulus candidate).natDegree := by
    change (rawFieldArrayPolynomial candidate.scalar).natDegree <
      (rawMaskPolynomial (rawFieldBitsToNat candidate.modulus)).natDegree
    rw [hmod.2]
    exact hscalarDegree
  exact AdjoinRoot.mk_ne_zero_of_natDegree_lt
    (by simpa [rawCandidateModulus] using hmod.1) hscalarNonzeroPoly hdegreeLt

end CorruptedFieldRecovery
