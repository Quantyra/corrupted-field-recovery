import CorruptedFieldRecovery.RawRabinCandidateCorrectness
import CorruptedFieldRecovery.RawExecutableTraceSemantic

/-! A proof-free outer entry point driven by the bounded Rabin gate. The
legacy candidate check appears only in a proposition-valued bridge; the Bool
path below evaluates the fast shape and Rabin checks. -/

namespace CorruptedFieldRecovery

/-- Turn a successful fast Bool into the proof expected by the semantic
coefficient lemmas. This theorem is used only for an erased proposition
argument; it is not called as a Bool computation. -/
theorem rawFieldCandidateFastCheck_to_legacyProof {s : Nat}
    (candidate : RawFieldCandidate s)
    (hfast : rawFieldCandidateFastCheck candidate = true) :
    rawFieldCandidateCheck candidate = true := by
  have hvalid := (rawFieldCandidateFastCheck_eq_true_iff_valid candidate).mp hfast
  change @decide (rawFieldCandidateValid candidate)
    (rawFieldCandidateValidDecidable candidate) = true
  exact (@decide_eq_true_eq (rawFieldCandidateValid candidate)
    (rawFieldCandidateValidDecidable candidate)).mpr hvalid

/-- The semantic verifier's decomposition and coordinate gates, with the
coefficient loop driven by the proof-erased candidate parameter. -/
def rawExecutableTraceFastCore {s R : Nat}
    (p : RawDecomposition (3 * s) R)
    (candidate : RawFieldCandidate s)
    (hfield : rawFieldCandidateCheck candidate = true)
    (forward inverse : RawCoordinateMatrix) : Bool :=
  rawDecompositionCheck p &&
    (rawCoordinateMatrixCheck (n := 3 * s) forward inverse &&
      rawExecutableTraceCompatibleCheck p.compatible candidate hfield inverse)

/-- Proof-free S011 verifier using the hfield-free finite Rabin scan. The
dependent branch creates only an erased proof for the existing semantic
coefficient functions; no legacy Bool candidate check occurs in this
definition's computational path. -/
def rawExecutableTraceFastVerifier {s R : Nat}
    (p : RawDecomposition (3 * s) R)
    (candidate : RawFieldCandidate s)
    (forward inverse : RawCoordinateMatrix) : Bool :=
  if hfast : rawFieldCandidateFastCheck candidate = true then
    rawExecutableTraceFastCore p candidate
      (rawFieldCandidateFastCheck_to_legacyProof candidate hfast) forward inverse
  else false

/-- Operational branch equation: after the single fast candidate gate passes,
the executable result is the decomposition/matrix/coefficient core. The
legacy candidate predicate occurs only in the erased proof argument. -/
theorem rawExecutableTraceFastVerifier_eq_core {s R : Nat}
    (p : RawDecomposition (3 * s) R)
    (candidate : RawFieldCandidate s)
    (forward inverse : RawCoordinateMatrix)
    (hfast : rawFieldCandidateFastCheck candidate = true) :
    rawExecutableTraceFastVerifier p candidate forward inverse =
      rawExecutableTraceFastCore p candidate
        (rawFieldCandidateFastCheck_to_legacyProof candidate hfast) forward inverse := by
  simp [rawExecutableTraceFastVerifier, hfast]

/-- Acceptance of the fast verifier proves the same literal trace-determinant
identity and residual support statement as the semantic verifier. -/
theorem accepted_rawExecutableTraceFastVerifier_sound {s R : Nat}
    (p : RawDecomposition (3 * s) R)
    (candidate : RawFieldCandidate s)
    (forward inverse : RawCoordinateMatrix)
    (hcheck : rawExecutableTraceFastVerifier p candidate forward inverse = true) :
    ∃ hfast : rawFieldCandidateFastCheck candidate = true,
      ∃ hcoordinates : rawCoordinateMatrixCheck (n := 3 * s) forward inverse = true,
        p.supportDimension ≤ R ∧
        AdjoinRoot.mk (rawCandidateModulus candidate)
          (rawCandidateScalar candidate) ≠ 0 ∧
        ∀ x y z,
          decodeRawArray (n := 3 * s) p.input x y z =
            rawTraceDetTensor candidate
              (rawFieldCandidateFastCheck_to_legacyProof candidate hfast)
              forward inverse hcoordinates x y z +
              pullback (decodeRawArray (n := p.supportDimension) p.residual)
                (rawSupportMap p.supportMatrix) x y z := by
  unfold rawExecutableTraceFastVerifier at hcheck
  split at hcheck
  · rename_i hfast
    have hfield := rawFieldCandidateFastCheck_to_legacyProof candidate hfast
    have hcore := hcheck
    simp only [rawExecutableTraceFastCore, Bool.and_eq_true] at hcore
    have hcoordinates : rawCoordinateMatrixCheck (n := 3 * s) forward inverse = true :=
      hcore.2.1
    have htrace := accepted_rawExecutableTraceCompatibleCheck_semantic
      p.compatible candidate hfield forward inverse hcoordinates hcore.2.2
    have hcombined : rawTraceDecompositionCheck p candidate hfield forward inverse
        hcoordinates = true := by
      simp only [rawTraceDecompositionCheck, Bool.and_eq_true]
      exact ⟨hcore.1, htrace⟩
    exact ⟨hfast, hcoordinates,
      accepted_rawDecompositionCheck_support_bound p hcore.1,
      accepted_rawCandidate_scalar_residue_ne_zero candidate hfield,
      accepted_rawTraceDecompositionCheck_sound p candidate hfield forward inverse
        hcoordinates hcombined⟩
  · simp at hcheck

end CorruptedFieldRecovery
