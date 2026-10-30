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

/-- The evaluator's canonical field coefficient equals the established
trace-determinant payload coefficient through the checked coordinate
equivalence, including the serialized scalar polynomial. -/
theorem rawPhysicalCanonicalTraceCoefficient_eq_payload {s : Nat}
    (candidate : RawFieldCandidate s)
    (hfield : rawFieldCandidateCheck candidate = true)
    (forward inverse : RawCoordinateMatrix)
    (hcoordinates : rawCoordinateMatrixCheck (n := 3 * s) forward inverse = true)
    (t : IncreasingTriple (3 * s)) :
    rawPhysicalCanonicalTraceCoefficient candidate hfield inverse t =
      rawTraceDetPayload candidate hfield forward inverse hcoordinates t := by
  have hv := accepted_rawFieldCandidateCheck candidate hfield
  have hm := rawFieldCandidateValid_modulus_polynomial candidate hv
  letI : Fact (Irreducible (rawCandidateModulus candidate)) :=
    ⟨accepted_rawCandidateModulus_irreducible candidate hfield⟩
  let K := AdjoinRoot (rawCandidateModulus candidate)
  letI : Module.Finite (ZMod 2) K := by
    simpa [rawCandidateModulus] using hm.1.finite_adjoinRoot
  let coords := accepted_rawCandidatePhysicalCoordinates candidate hfield
    forward inverse hcoordinates
  have hscalar :
      rawCandidateQuotientClass candidate (rawFieldBitsToNat candidate.scalar) =
        AdjoinRoot.mk (rawCandidateModulus candidate) (rawCandidateScalar candidate) := by
    rw [rawCandidateQuotientClass, rawCandidateScalar, rawFieldArrayPolynomial_eq_mask]
  have hi := accepted_rawCandidatePhysicalCoordinates_symm_eq_powerBasisInverse
    candidate hfield forward inverse hcoordinates
    (coordinateVectorCode (increasingTripleI t))
  have hj := accepted_rawCandidatePhysicalCoordinates_symm_eq_powerBasisInverse
    candidate hfield forward inverse hcoordinates
    (coordinateVectorCode (increasingTripleJ t))
  have hk := accepted_rawCandidatePhysicalCoordinates_symm_eq_powerBasisInverse
    candidate hfield forward inverse hcoordinates
    (coordinateVectorCode (increasingTripleK t))
  have hi' : rawPhysicalCanonicalTriple candidate hfield inverse
      (coordinateVectorCode (increasingTripleI t)) = coords.symm
        (coordinateVectorCode (increasingTripleI t)) := by
    simpa [rawPhysicalCanonicalTriple, coords] using hi.symm
  have hj' : rawPhysicalCanonicalTriple candidate hfield inverse
      (coordinateVectorCode (increasingTripleJ t)) = coords.symm
        (coordinateVectorCode (increasingTripleJ t)) := by
    simpa [rawPhysicalCanonicalTriple, coords] using hj.symm
  have hk' : rawPhysicalCanonicalTriple candidate hfield inverse
      (coordinateVectorCode (increasingTripleK t)) = coords.symm
        (coordinateVectorCode (increasingTripleK t)) := by
    simpa [rawPhysicalCanonicalTriple, coords] using hk.symm
  unfold rawPhysicalCanonicalTraceCoefficient rawTraceDetPayload
  rw [hi', hj', hk', hscalar]

end CorruptedFieldRecovery
