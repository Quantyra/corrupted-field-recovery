import CorruptedFieldRecovery.RawExecutableTraceSemantic

/-! Standalone certificate consequences of the proof-free executable verifier.
This records field size, nonzero scalar, matrix decoding, supported residual
rank, and the exact all-vector representation identity. -/

namespace CorruptedFieldRecovery

/-- A tensor pulled back through a `d`-dimensional serialized support map has
mode-image rank at most `d`. -/
theorem modeImage_pullback_finrank_le_supportDimension {n d R : Nat}
    (E : BinaryTensor d)
    (u : BinaryVector n →ₗ[ZMod 2] BinaryVector d)
    (hd : d ≤ R) :
    Module.finrank (ZMod 2) (modeImage (pullback E u)) ≤ R := by
  have hdim : Module.finrank (ZMod 2) (BinaryVector d) = d := by
    rw [Module.finrank_eq_card_basis (Pi.basisFun (ZMod 2) (Fin d))]
    simp
  calc
    Module.finrank (ZMod 2) (modeImage (pullback E u)) ≤
        Module.finrank (ZMod 2) (LinearMap.range u.dualMap) :=
      Submodule.finrank_mono (modeImage_pullback_le_dualMap_range E u)
    _ ≤ Module.finrank (ZMod 2) (BinaryVector d →ₗ[ZMod 2] ZMod 2) :=
      LinearMap.finrank_range_le u.dualMap
    _ = d := by
      rw [Subspace.dual_finrank_eq, hdim]
    _ ≤ R := hd

/-- Standalone S011 verifier theorem. A true raw Bool result supplies accepted
candidate and matrix witnesses; these imply exact field cardinality, a nonzero
scalar residue, bounded support rank, and the full semantic decomposition. -/
theorem accepted_rawExecutableTraceCertificate_sound {s R : Nat}
    (p : RawDecomposition (3 * s) R)
    (candidate : RawFieldCandidate s)
    (forward inverse : RawCoordinateMatrix)
    (hcheck : rawExecutableTraceVerifier p candidate forward inverse = true) :
    ∃ hfield : rawFieldCandidateCheck candidate = true,
      ∃ hcoordinates : rawCoordinateMatrixCheck (n := 3 * s) forward inverse = true,
        Nat.card (AdjoinRoot (rawCandidateModulus candidate)) = 2 ^ s ∧
          AdjoinRoot.mk (rawCandidateModulus candidate) (rawCandidateScalar candidate) ≠ 0 ∧
          Module.finrank (ZMod 2)
              (modeImage (pullback (decodeRawArray (n := p.supportDimension) p.residual)
                (rawSupportMap (n := 3 * s) p.supportMatrix))) ≤ R ∧
          (∀ v : BinaryVector (3 * s),
            (accepted_rawCandidatePhysicalCoordinates candidate hfield forward inverse
              hcoordinates).symm v =
                (accepted_rawCandidatePowerBasisCoordinates candidate hfield).symm
                  (rawCoordinateMatrixMap inverse v)) ∧
          ∀ x y z,
            decodeRawArray (n := 3 * s) p.input x y z =
              rawTraceDetTensor candidate hfield forward inverse hcoordinates x y z +
                pullback (decodeRawArray (n := p.supportDimension) p.residual)
                  (rawSupportMap p.supportMatrix) x y z := by
  obtain ⟨hfield, hcoordinates, hsupport, hscalar, hrepr⟩ :=
    accepted_rawExecutableTraceVerifier_sound p candidate forward inverse hcheck
  refine ⟨hfield, hcoordinates, accepted_rawCandidate_quotient_card candidate hfield,
    hscalar, ?_, ?_, hrepr⟩
  · exact modeImage_pullback_finrank_le_supportDimension
      (decodeRawArray (n := p.supportDimension) p.residual)
      (rawSupportMap p.supportMatrix) hsupport
  · intro v
    exact accepted_rawCandidatePhysicalCoordinates_symm_eq_powerBasisInverse
      candidate hfield forward inverse hcoordinates v

end CorruptedFieldRecovery
