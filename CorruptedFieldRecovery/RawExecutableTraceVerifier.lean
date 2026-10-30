import CorruptedFieldRecovery.RawTraceDecomposition
import CorruptedFieldRecovery.RawPhysicalTraceComposition

/-! A serialized coefficient loop whose entries are computed by the actual
Nat-mask physical trace evaluator. The checked field candidate and coordinate
matrix remain explicit inputs to the verifier. -/

namespace CorruptedFieldRecovery

private theorem zmodTwo_if_eq_zero (x : ZMod 2) :
    (if x = 0 then (0 : ZMod 2) else 1) = x := by
  fin_cases x <;> decide

/-- Compute one increasing coefficient by evaluating the raw determinant
trace bit on the three coordinate unit vectors. -/
def rawExecutableTraceCoefficient {s : Nat}
    (candidate : RawFieldCandidate s)
    (hfield : rawFieldCandidateCheck candidate = true)
    (inverse : RawCoordinateMatrix) (t : IncreasingTriple (3 * s)) : ZMod 2 :=
  (rawPhysicalTraceDet3Bits candidate hfield inverse
    (coordinateVectorCode (increasingTripleI t))
    (coordinateVectorCode (increasingTripleJ t))
    (coordinateVectorCode (increasingTripleK t)) : Nat)

/-- Semantic field coefficient associated with the exact canonical triples
decoded from the checked inverse-matrix outputs. -/
noncomputable def rawPhysicalCanonicalTraceCoefficient {s : Nat}
    (candidate : RawFieldCandidate s)
    (hfield : rawFieldCandidateCheck candidate = true)
    (inverse : RawCoordinateMatrix) (t : IncreasingTriple (3 * s)) : ZMod 2 := by
  have hv := accepted_rawFieldCandidateCheck candidate hfield
  have hm := rawFieldCandidateValid_modulus_polynomial candidate hv
  letI : Fact (Irreducible (rawCandidateModulus candidate)) :=
    ⟨accepted_rawCandidateModulus_irreducible candidate hfield⟩
  let K := AdjoinRoot (rawCandidateModulus candidate)
  letI : Module.Finite (ZMod 2) K := by
    simpa [rawCandidateModulus] using hm.1.finite_adjoinRoot
  exact Algebra.trace (ZMod 2) K
    (rawCandidateQuotientClass candidate (rawFieldBitsToNat candidate.scalar) *
      fieldDet3
        (rawPhysicalCanonicalTriple candidate hfield inverse
          (coordinateVectorCode (increasingTripleI t)))
        (rawPhysicalCanonicalTriple candidate hfield inverse
          (coordinateVectorCode (increasingTripleJ t)))
        (rawPhysicalCanonicalTriple candidate hfield inverse
          (coordinateVectorCode (increasingTripleK t))))

/-- Each raw Nat evaluator output, cast to the base field, equals the literal
algebraic trace of the determinant on the decoded power-basis triples. -/
theorem rawExecutableTraceCoefficient_eq_semantic {s : Nat}
    (candidate : RawFieldCandidate s)
    (hfield : rawFieldCandidateCheck candidate = true)
    (inverse : RawCoordinateMatrix) (t : IncreasingTriple (3 * s)) :
    rawExecutableTraceCoefficient candidate hfield inverse t =
      rawPhysicalCanonicalTraceCoefficient candidate hfield inverse t := by
  let τ := rawPhysicalCanonicalTraceCoefficient candidate hfield inverse t
  have hbit := rawPhysicalTraceDet3Bits_eq_canonicalTrace candidate hfield inverse
    (coordinateVectorCode (increasingTripleI t))
    (coordinateVectorCode (increasingTripleJ t))
    (coordinateVectorCode (increasingTripleK t))
  change (rawPhysicalTraceDet3Bits candidate hfield inverse
    (coordinateVectorCode (increasingTripleI t))
    (coordinateVectorCode (increasingTripleJ t))
    (coordinateVectorCode (increasingTripleK t)) : ZMod 2) = τ
  rw [hbit]
  simpa only [Nat.cast_ite, Nat.cast_zero, Nat.cast_one] using zmodTwo_if_eq_zero τ

/-- The executable coefficient loop checks every serialized increasing slot
against the raw trace evaluator. -/
def rawExecutableTraceCompatibleCheck {s : Nat}
    (compatible : RawBinaryArray)
    (candidate : RawFieldCandidate s)
    (hfield : rawFieldCandidateCheck candidate = true)
    (inverse : RawCoordinateMatrix) : Bool :=
  decide (compatible.size = (3 * s) * (3 * s) * (3 * s)) &&
    decide (∀ t : IncreasingTriple (3 * s),
      compatible[rawCoefficientOffset (3 * s)
        (increasingTripleI t) (increasingTripleJ t) (increasingTripleK t)]! =
        rawExecutableTraceCoefficient candidate hfield inverse t)

/-- An accepted executable loop certifies each stored coefficient directly
against the Nat-mask computation. -/
theorem accepted_rawExecutableTraceCompatibleCheck {s : Nat}
    (compatible : RawBinaryArray)
    (candidate : RawFieldCandidate s)
    (hfield : rawFieldCandidateCheck candidate = true)
    (inverse : RawCoordinateMatrix)
    (hcheck : rawExecutableTraceCompatibleCheck compatible candidate hfield inverse = true) :
    ∀ t : IncreasingTriple (3 * s),
      compatible[rawCoefficientOffset (3 * s)
        (increasingTripleI t) (increasingTripleJ t) (increasingTripleK t)]! =
        rawExecutableTraceCoefficient candidate hfield inverse t := by
  simp only [rawExecutableTraceCompatibleCheck, Bool.and_eq_true] at hcheck
  exact of_decide_eq_true hcheck.2

/-- The full raw verifier combines the existing compatible-plus-residual
decomposition gate with the executable trace coefficient loop. -/
def rawExecutableTraceDecompositionCheck {s R : Nat}
    (p : RawDecomposition (3 * s) R)
    (candidate : RawFieldCandidate s)
    (hfield : rawFieldCandidateCheck candidate = true)
    (forward inverse : RawCoordinateMatrix) : Bool :=
  rawDecompositionCheck p && (rawFieldCandidateCheck candidate &&
    (rawCoordinateMatrixCheck (n := 3 * s) forward inverse &&
      rawExecutableTraceCompatibleCheck p.compatible candidate hfield inverse))

/-- Acceptance retains the checked support bound and proves the represented
input equals the serialized compatible tensor plus its explicitly factored
residual; the compatible array is constrained by the executable loop. -/
theorem accepted_rawExecutableTraceDecompositionCheck {s R : Nat}
    (p : RawDecomposition (3 * s) R)
    (candidate : RawFieldCandidate s)
    (hfield : rawFieldCandidateCheck candidate = true)
    (forward inverse : RawCoordinateMatrix)
    (hcheck : rawExecutableTraceDecompositionCheck p candidate hfield forward inverse = true) :
    p.supportDimension ≤ R ∧
      (∀ x y z, decodeRawArray (n := 3 * s) p.input x y z =
        decodeRawArray (n := 3 * s) p.compatible x y z +
          pullback (decodeRawArray (n := p.supportDimension) p.residual)
            (rawSupportMap p.supportMatrix) x y z) ∧
      (∀ t : IncreasingTriple (3 * s),
        p.compatible[rawCoefficientOffset (3 * s)
          (increasingTripleI t) (increasingTripleJ t) (increasingTripleK t)]! =
          rawExecutableTraceCoefficient candidate hfield inverse t) := by
  simp only [rawExecutableTraceDecompositionCheck, Bool.and_eq_true] at hcheck
  refine ⟨accepted_rawDecompositionCheck_support_bound p hcheck.1, ?_,
    accepted_rawExecutableTraceCompatibleCheck p.compatible candidate hfield inverse hcheck.2.2.2⟩
  intro x y z
  exact accepted_rawDecompositionCheck_sound p hcheck.1 x y z

end CorruptedFieldRecovery
