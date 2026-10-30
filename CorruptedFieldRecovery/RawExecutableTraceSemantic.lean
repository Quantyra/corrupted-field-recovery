import CorruptedFieldRecovery.RawExecutableTraceVerifier

/-! Semantic correspondence between the executable inverse-matrix route and
the accepted coordinate equivalence used by the trace tensor. -/

namespace CorruptedFieldRecovery

private theorem linearEquiv_symm_eq_of_leftInverse
    {V W : Type*} [AddCommMonoid V] [AddCommMonoid W]
    [Module (ZMod 2) V] [Module (ZMod 2) W]
    (e : V ≃ₗ[ZMod 2] W) (g : W →ₗ[ZMod 2] V)
    (h : ∀ x, g (e x) = x) : ∀ y, e.symm y = g y := by
  intro y
  calc
    e.symm y = g (e (e.symm y)) := (h _).symm
    _ = g y := congrArg g (e.apply_symm_apply y)

/-- The accepted matrix equivalence decodes vectors by the serialized inverse
matrix. This uses both checked matrix products, not an assumed inverse law. -/
theorem accepted_rawCoordinateMatrixEquiv_symm_apply {n : Nat}
    (forward inverse : RawCoordinateMatrix)
    (hcheck : rawCoordinateMatrixCheck (n := n) forward inverse = true)
    (v : BinaryVector n) :
    (accepted_rawCoordinateMatrixEquiv forward inverse hcheck).symm v =
      rawCoordinateMatrixMap inverse v := by
  let e := accepted_rawCoordinateMatrixEquiv forward inverse hcheck
  have hcomp := accepted_rawCoordinateMatrixCheck_compositions forward inverse hcheck
  have hleft : rawCoordinateMatrixMap forward (rawCoordinateMatrixMap inverse v) = v := by
    have h := congrArg (fun f : BinaryVector n →ₗ[ZMod 2] BinaryVector n => f v) hcomp.2
    simpa [LinearMap.comp_apply] using h
  apply linearEquiv_symm_eq_of_leftInverse e (rawCoordinateMatrixMap inverse)
  intro x
  have h := congrArg (fun f : BinaryVector n →ₗ[ZMod 2] BinaryVector n => f x) hcomp.1
  simpa [LinearMap.comp_apply] using h

/-- Decoding the checked physical coordinate isomorphism agrees exactly with
first applying the raw inverse matrix and then decoding the canonical power
basis. -/
theorem accepted_rawCandidatePhysicalCoordinates_symm_eq_powerBasisInverse
    {s : Nat} (candidate : RawFieldCandidate s)
    (hfield : rawFieldCandidateCheck candidate = true)
    (forward inverse : RawCoordinateMatrix)
    (hcoordinates : rawCoordinateMatrixCheck (n := 3 * s) forward inverse = true)
    (v : BinaryVector (3 * s)) :
    (accepted_rawCandidatePhysicalCoordinates candidate hfield forward inverse
      hcoordinates).symm v =
      (accepted_rawCandidatePowerBasisCoordinates candidate hfield).symm
        (rawCoordinateMatrixMap inverse v) := by
  change (accepted_rawCandidatePowerBasisCoordinates candidate hfield).symm
      ((accepted_rawCoordinateMatrixEquiv forward inverse hcoordinates).symm v) = _
  rw [accepted_rawCoordinateMatrixEquiv_symm_apply]

end CorruptedFieldRecovery
