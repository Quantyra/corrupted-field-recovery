import CorruptedFieldRecovery.RawCoordinateEquivalence
import CorruptedFieldRecovery.FourContractions

/-! Coordinate transport from the quotient power basis to the physical
`3s` binary coordinates.  This is the canonical coordinate map; the raw
matrix equivalence is composed only after its checker has been accepted. -/

namespace CorruptedFieldRecovery

open AdjoinRoot

/-- The power-basis coefficients of one quotient-field element, indexed by
the degree parameter rather than the polynomial's degree expression. -/
noncomputable def rawQuotientPowerCoordinates {s : Nat}
    (p : Polynomial (ZMod 2)) (hmonic : p.Monic)
    (hdegree : p.natDegree = s) :
    AdjoinRoot p ≃ₗ[ZMod 2] (Fin s → ZMod 2) := by
  let b : Module.Basis (Fin s) (ZMod 2) (AdjoinRoot p) :=
    (AdjoinRoot.powerBasisAux' hmonic).reindex (finCongr hdegree)
  exact b.equivFun

/-- Interpret a triple of quotient elements by its three power-basis
coefficient blocks, in row-major `Fin 3 × Fin s` order. -/
noncomputable def rawFieldTriplePowerCoordinates {s : Nat}
    (p : Polynomial (ZMod 2)) (hmonic : p.Monic)
    (hdegree : p.natDegree = s) :
    FieldTriple (AdjoinRoot p) ≃ₗ[ZMod 2] (Fin 3 × Fin s → ZMod 2) where
  toFun x ij :=
    if ij.1 = 0 then rawQuotientPowerCoordinates p hmonic hdegree x.1 ij.2
    else if ij.1 = 1 then
      rawQuotientPowerCoordinates p hmonic hdegree x.2.1 ij.2
    else rawQuotientPowerCoordinates p hmonic hdegree x.2.2 ij.2
  invFun f :=
    ((rawQuotientPowerCoordinates p hmonic hdegree).symm
      (fun j => f (0, j)),
     (rawQuotientPowerCoordinates p hmonic hdegree).symm
      (fun j => f (1, j)),
     (rawQuotientPowerCoordinates p hmonic hdegree).symm
      (fun j => f (2, j)))
  left_inv := by
    intro x
    rcases x with ⟨x0, x1, x2⟩
    apply Prod.ext
    · exact (rawQuotientPowerCoordinates p hmonic hdegree).symm_apply_apply x0
    · apply Prod.ext
      · exact (rawQuotientPowerCoordinates p hmonic hdegree).symm_apply_apply x1
      · exact (rawQuotientPowerCoordinates p hmonic hdegree).symm_apply_apply x2
  right_inv := by
    intro f
    funext ij
    rcases ij with ⟨i, j⟩
    fin_cases i
    · change (rawQuotientPowerCoordinates p hmonic hdegree)
        ((rawQuotientPowerCoordinates p hmonic hdegree).symm
          (fun j => f (0, j))) j = f (0, j)
      exact congrArg (fun g : Fin s → ZMod 2 => g j)
        ((rawQuotientPowerCoordinates p hmonic hdegree).apply_symm_apply
          (fun j => f (0, j)))
    · change (rawQuotientPowerCoordinates p hmonic hdegree)
        ((rawQuotientPowerCoordinates p hmonic hdegree).symm
          (fun j => f (1, j))) j = f (1, j)
      exact congrArg (fun g : Fin s → ZMod 2 => g j)
        ((rawQuotientPowerCoordinates p hmonic hdegree).apply_symm_apply
          (fun j => f (1, j)))
    · change (rawQuotientPowerCoordinates p hmonic hdegree)
        ((rawQuotientPowerCoordinates p hmonic hdegree).symm
          (fun j => f (2, j))) j = f (2, j)
      exact congrArg (fun g : Fin s → ZMod 2 => g j)
        ((rawQuotientPowerCoordinates p hmonic hdegree).apply_symm_apply
          (fun j => f (2, j)))
  map_add' := by
    intro x y
    funext ij
    rcases ij with ⟨i, j⟩
    fin_cases i <;> simp [rawQuotientPowerCoordinates]
  map_smul' := by
    intro c x
    funext ij
    rcases ij with ⟨i, j⟩
    fin_cases i <;> simp [rawQuotientPowerCoordinates]

/-- Reindex the three power-basis blocks as a single physical binary vector
of length `3*s`. -/
noncomputable def rawFieldTripleToBinaryVector {s : Nat}
    (p : Polynomial (ZMod 2)) (hmonic : p.Monic)
    (hdegree : p.natDegree = s) :
    FieldTriple (AdjoinRoot p) ≃ₗ[ZMod 2] BinaryVector (3 * s) := by
  let coord := rawFieldTriplePowerCoordinates p hmonic hdegree
  let idx : Fin 3 × Fin s ≃ Fin (3 * s) := finProdFinEquiv
  refine
    { toFun := fun x k => coord x (idx.symm k)
      invFun := fun v => coord.symm (fun ij => v (idx ij))
      left_inv := by
        intro x
        apply coord.injective
        funext ij
        simp [idx]
      right_inv := by
        intro v
        funext k
        calc
          coord (coord.symm (fun ij => v (idx ij))) (idx.symm k) =
              (fun ij => v (idx ij)) (idx.symm k) := by
            rw [coord.apply_symm_apply]
          _ = v k := by
            change v (idx (idx.symm k)) = v k
            exact congrArg v (idx.apply_symm_apply k)
      map_add' := by
        intro x y
        funext k
        simp [coord]
      map_smul' := by
        intro c x
        funext k
        simp [coord] }

/-- A checked raw square matrix, after the canonical power-basis coordinate
identification, gives an equivalence from quotient-field triples to the
physical `3*s`-bit vector space. -/
noncomputable def accepted_rawCandidatePowerBasisCoordinates {s : Nat}
    (candidate : RawFieldCandidate s)
    (hcheck : rawFieldCandidateCheck candidate = true) :
    FieldTriple (AdjoinRoot (rawCandidateModulus candidate)) ≃ₗ[ZMod 2]
      BinaryVector (3 * s) := by
  have hvalid := accepted_rawFieldCandidateCheck candidate hcheck
  have hmod := rawFieldCandidateValid_modulus_polynomial candidate hvalid
  letI : Fact (Irreducible (rawCandidateModulus candidate)) :=
    ⟨accepted_rawCandidateModulus_irreducible candidate hcheck⟩
  exact rawFieldTripleToBinaryVector (rawCandidateModulus candidate) hmod.1
    (by simpa [rawCandidateModulus] using hmod.2)

noncomputable def accepted_rawCandidatePhysicalCoordinates {s : Nat}
    (candidate : RawFieldCandidate s)
    (hcheck : rawFieldCandidateCheck candidate = true)
    (forward inverse : RawCoordinateMatrix)
    (hmatrix : rawCoordinateMatrixCheck (n := 3 * s) forward inverse = true) :
    FieldTriple (AdjoinRoot (rawCandidateModulus candidate)) ≃ₗ[ZMod 2]
      BinaryVector (3 * s) := by
  exact (accepted_rawCandidatePowerBasisCoordinates candidate hcheck).trans
    (accepted_rawCoordinateMatrixEquiv forward inverse hmatrix)

end CorruptedFieldRecovery
