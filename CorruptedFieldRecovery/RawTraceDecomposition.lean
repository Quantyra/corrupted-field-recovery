import CorruptedFieldRecovery.RawVerifier
import CorruptedFieldRecovery.RawFieldCoordinateBridge
import CorruptedFieldRecovery.FourContractions

/-! S011 trace-compatible coefficient validation.

The supplied compatible array is checked against coefficients computed from
the accepted quotient-field scalar and the checked physical coordinates.  The
expected tensor is decoded from those computed alternating coefficients; no
identity is stored in the certificate.  The construction is noncomputable at
the current quotient-field boundary, so this is a formal finite coefficient
checker, not yet a serialized bit-level implementation of quotient arithmetic.
-/

namespace CorruptedFieldRecovery

open AdjoinRoot

private theorem fieldDet3_zero_first {K : Type*} [CommRing K]
    (x z : FieldTriple K) : fieldDet3 x x z = 0 := by
  simp [fieldDet3]
  ring

private theorem fieldDet3_zero_middle {K : Type*} [CommRing K]
    (x y : FieldTriple K) : fieldDet3 x y x = 0 := by
  simp [fieldDet3]
  ring

private theorem fieldDet3_zero_last {K : Type*} [CommRing K]
    (x y : FieldTriple K) : fieldDet3 x y y = 0 := by
  simp [fieldDet3]
  ring

private noncomputable def traceScaleLinear {K : Type*} [Field K] [Algebra (ZMod 2) K]
    [Module.Finite (ZMod 2) K] (c : K) : K →ₗ[ZMod 2] ZMod 2 :=
  (Algebra.trace (ZMod 2) K).comp
    ({ toFun := fun x => c * x
       map_add' := by intro x y; simp [mul_add]
       map_smul' := by
         intro a x
         change c * (a • x) = a • (c * x)
         rw [Algebra.smul_def, Algebra.smul_def]
         ring } : K →ₗ[ZMod 2] K)

private theorem updateVec3_first {V : Type*} [Add V] (x y z v : V) :
    Function.update ![x, y, z] (0 : Fin 3) v = ![v, y, z] := by
  funext i
  fin_cases i <;> simp

private theorem updateVec3_middle {V : Type*} [Add V] (x y z v : V) :
    Function.update ![x, y, z] (1 : Fin 3) v = ![x, v, z] := by
  funext i
  fin_cases i <;> simp

private theorem updateVec3_last {V : Type*} [Add V] (x y z v : V) :
    Function.update ![x, y, z] (2 : Fin 3) v = ![x, y, v] := by
  funext i
  fin_cases i <;> simp

/-- Curry a ternary multilinear map on `Fin 3` into the nested linear-map
representation used by `BinaryTensor`. The three linearity obligations are
inherited directly from `MultilinearMap.map_update_add` and
`MultilinearMap.map_update_smul`. -/
private def curryBinaryTensor {n : Nat}
    (m : MultilinearMap (ZMod 2) (fun _ : Fin 3 => BinaryVector n) (ZMod 2)) :
    BinaryTensor n := by
  classical
  refine
    { toFun := fun x =>
        { toFun := fun y =>
            { toFun := fun z => m ![x, y, z]
              map_add' := ?_
              map_smul' := ?_ }
          map_add' := ?_
          map_smul' := ?_ }
      map_add' := ?_
      map_smul' := ?_ }
  · intro z w
    calc
      m ![x, y, z + w] = m (Function.update ![x, y, z] (2 : Fin 3) (z + w)) := by
        rw [updateVec3_last x y z (z + w)]
      _ = m (Function.update ![x, y, z] (2 : Fin 3) z) +
          m (Function.update ![x, y, z] (2 : Fin 3) w) :=
        m.map_update_add ![x, y, z] (2 : Fin 3) z w
      _ = m ![x, y, z] + m ![x, y, w] := by
        rw [updateVec3_last x y z z, updateVec3_last x y z w]
  · intro a z
    calc
      m ![x, y, a • z] = m (Function.update ![x, y, z] (2 : Fin 3) (a • z)) := by
        rw [updateVec3_last x y z (a • z)]
      _ = a • m (Function.update ![x, y, z] (2 : Fin 3) z) :=
        m.map_update_smul ![x, y, z] (2 : Fin 3) a z
      _ = a • m ![x, y, z] := by rw [updateVec3_last x y z z]
  · intro y w
    apply LinearMap.ext
    intro z
    calc
      m ![x, y + w, z] = m (Function.update ![x, y, z] (1 : Fin 3) (y + w)) := by
        rw [updateVec3_middle x y z (y + w)]
      _ = m (Function.update ![x, y, z] (1 : Fin 3) y) +
          m (Function.update ![x, y, z] (1 : Fin 3) w) :=
        m.map_update_add ![x, y, z] (1 : Fin 3) y w
      _ = m ![x, y, z] + m ![x, w, z] := by
        rw [updateVec3_middle x y z y, updateVec3_middle x y z w]
  · intro a y
    apply LinearMap.ext
    intro z
    calc
      m ![x, a • y, z] = m (Function.update ![x, y, z] (1 : Fin 3) (a • y)) := by
        rw [updateVec3_middle x y z (a • y)]
      _ = a • m (Function.update ![x, y, z] (1 : Fin 3) y) :=
        m.map_update_smul ![x, y, z] (1 : Fin 3) a y
      _ = a • m ![x, y, z] := by rw [updateVec3_middle x y z y]
  · intro x y
    apply LinearMap.ext
    intro z
    apply LinearMap.ext
    intro w
    calc
      m ![x + y, z, w] = m (Function.update ![x, z, w] (0 : Fin 3) (x + y)) := by
        rw [updateVec3_first x z w (x + y)]
      _ = m (Function.update ![x, z, w] (0 : Fin 3) x) +
          m (Function.update ![x, z, w] (0 : Fin 3) y) :=
        m.map_update_add ![x, z, w] (0 : Fin 3) x y
      _ = m ![x, z, w] + m ![y, z, w] := by
        rw [updateVec3_first x z w x, updateVec3_first x z w y]
  · intro a x
    apply LinearMap.ext
    intro z
    apply LinearMap.ext
    intro w
    calc
      m ![a • x, z, w] = m (Function.update ![x, z, w] (0 : Fin 3) (a • x)) := by
        rw [updateVec3_first x z w (a • x)]
      _ = a • m (Function.update ![x, z, w] (0 : Fin 3) x) :=
        m.map_update_smul ![x, z, w] (0 : Fin 3) a x
      _ = a • m ![x, z, w] := by rw [updateVec3_first x z w x]

/-- Pointwise trace of a scaled field determinant, transported along a binary
linear coordinate map. The multilinearity is built by composing the library's
alternating basis determinant with the coordinate maps and trace map. -/
noncomputable def traceDeterminantTensor {n : Nat}
    (K : Type*) [Field K] [Algebra (ZMod 2) K] [Module.Finite (ZMod 2) K]
    (c : K) (coords : BinaryVector n →ₗ[ZMod 2] FieldTriple K) : BinaryTensor n := by
  let det : MultilinearMap (ZMod 2) (fun _ : Fin 3 => FieldTriple K) K :=
    (fieldTripleStandardBasis K).det.toMultilinearMap.restrictScalars (ZMod 2)
  let coordFamily : ∀ _ : Fin 3, BinaryVector n →ₗ[ZMod 2] FieldTriple K := fun _ => coords
  let transported := det.compLinearMap coordFamily
  exact curryBinaryTensor ((traceScaleLinear c).compMultilinearMap transported)

theorem traceDeterminantTensor_apply {n : Nat}
    (K : Type*) [Field K] [Algebra (ZMod 2) K] [Module.Finite (ZMod 2) K]
    (c : K) (coords : BinaryVector n →ₗ[ZMod 2] FieldTriple K)
    (x y z : BinaryVector n) :
    traceDeterminantTensor K c coords x y z =
      Algebra.trace (ZMod 2) K (c * fieldDet3 (coords x) (coords y) (coords z)) := by
  have hcoord : (fun i : Fin 3 => coords (![x, y, z] i)) = ![coords x, coords y, coords z] := by
    funext i
    fin_cases i <;> rfl
  simp [traceDeterminantTensor, curryBinaryTensor, traceScaleLinear, hcoord,
    fieldDet3_eq_standardBasis_det]

/-- Repeated arguments make the determinant zero, so the transported trace
form is alternating. -/
theorem traceDeterminantTensor_alternating {n : Nat}
    (K : Type*) [Field K] [Algebra (ZMod 2) K] [Module.Finite (ZMod 2) K]
    (c : K) (coords : BinaryVector n →ₗ[ZMod 2] FieldTriple K) :
    IsAlternating (traceDeterminantTensor K c coords) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x z
    rw [traceDeterminantTensor_apply, fieldDet3_zero_first]
    simp
  · intro x y
    rw [traceDeterminantTensor_apply, fieldDet3_zero_middle]
    simp
  · intro x y
    rw [traceDeterminantTensor_apply, fieldDet3_zero_last]
    simp

/-- The expected increasing coefficients, evaluated from the actual
candidate field, nonzero scalar, and accepted physical coordinate map. -/
noncomputable def rawTraceDetPayload {s : Nat}
    (candidate : RawFieldCandidate s)
    (hfield : rawFieldCandidateCheck candidate = true)
    (forward inverse : RawCoordinateMatrix)
    (hcoordinates : rawCoordinateMatrixCheck (n := 3 * s) forward inverse = true) :
    DenseInputPayload (3 * s) := by
  have hvalid := accepted_rawFieldCandidateCheck candidate hfield
  have hmod := rawFieldCandidateValid_modulus_polynomial candidate hvalid
  letI : Fact (Irreducible (rawCandidateModulus candidate)) :=
    ⟨accepted_rawCandidateModulus_irreducible candidate hfield⟩
  let K := AdjoinRoot (rawCandidateModulus candidate)
  letI : Module.Finite (ZMod 2) K := by
    simpa [rawCandidateModulus] using hmod.1.finite_adjoinRoot
  let coords := accepted_rawCandidatePhysicalCoordinates candidate hfield
    forward inverse hcoordinates
  let c : K := AdjoinRoot.mk (rawCandidateModulus candidate)
    (rawCandidateScalar candidate)
  intro t
  exact Algebra.trace (ZMod 2) K
    (c * fieldDet3 (coords.symm (coordinateVectorCode (increasingTripleI t)))
      (coords.symm (coordinateVectorCode (increasingTripleJ t)))
      (coords.symm (coordinateVectorCode (increasingTripleK t))))

/-- The pointwise trace-determinant tensor computed from the accepted field
candidate and physical coordinates. -/
noncomputable def rawTraceDetTensor {s : Nat}
    (candidate : RawFieldCandidate s)
    (hfield : rawFieldCandidateCheck candidate = true)
    (forward inverse : RawCoordinateMatrix)
    (hcoordinates : rawCoordinateMatrixCheck (n := 3 * s) forward inverse = true) :
    BinaryTensor (3 * s) := by
  have hvalid := accepted_rawFieldCandidateCheck candidate hfield
  have hmod := rawFieldCandidateValid_modulus_polynomial candidate hvalid
  letI : Fact (Irreducible (rawCandidateModulus candidate)) :=
    ⟨accepted_rawCandidateModulus_irreducible candidate hfield⟩
  let K := AdjoinRoot (rawCandidateModulus candidate)
  letI : Module.Finite (ZMod 2) K := by
    simpa [rawCandidateModulus] using hmod.1.finite_adjoinRoot
  let coords := accepted_rawCandidatePhysicalCoordinates candidate hfield
    forward inverse hcoordinates
  let c : K := AdjoinRoot.mk (rawCandidateModulus candidate)
    (rawCandidateScalar candidate)
  exact traceDeterminantTensor K c coords.symm.toLinearMap

theorem rawTraceDetTensor_alternating {s : Nat}
    (candidate : RawFieldCandidate s)
    (hfield : rawFieldCandidateCheck candidate = true)
    (forward inverse : RawCoordinateMatrix)
    (hcoordinates : rawCoordinateMatrixCheck (n := 3 * s) forward inverse = true) :
    IsAlternating (rawTraceDetTensor candidate hfield forward inverse hcoordinates) := by
  have hvalid := accepted_rawFieldCandidateCheck candidate hfield
  have hmod := rawFieldCandidateValid_modulus_polynomial candidate hvalid
  letI : Fact (Irreducible (rawCandidateModulus candidate)) :=
    ⟨accepted_rawCandidateModulus_irreducible candidate hfield⟩
  let K := AdjoinRoot (rawCandidateModulus candidate)
  letI : Module.Finite (ZMod 2) K := by
    simpa [rawCandidateModulus] using hmod.1.finite_adjoinRoot
  let coords := accepted_rawCandidatePhysicalCoordinates candidate hfield
    forward inverse hcoordinates
  let c : K := AdjoinRoot.mk (rawCandidateModulus candidate)
    (rawCandidateScalar candidate)
  simpa [rawTraceDetTensor, K, coords, c] using
    traceDeterminantTensor_alternating K c coords.symm.toLinearMap

/-- The payload is exactly the increasing coefficient table of the literal
pointwise trace-determinant tensor. -/
theorem rawTraceDetPayload_eq_encode {s : Nat}
    (candidate : RawFieldCandidate s)
    (hfield : rawFieldCandidateCheck candidate = true)
    (forward inverse : RawCoordinateMatrix)
    (hcoordinates : rawCoordinateMatrixCheck (n := 3 * s) forward inverse = true) :
    rawTraceDetPayload candidate hfield forward inverse hcoordinates =
      encodeDenseInput (rawTraceDetTensor candidate hfield forward inverse hcoordinates) := by
  have hvalid := accepted_rawFieldCandidateCheck candidate hfield
  have hmod := rawFieldCandidateValid_modulus_polynomial candidate hvalid
  letI : Fact (Irreducible (rawCandidateModulus candidate)) :=
    ⟨accepted_rawCandidateModulus_irreducible candidate hfield⟩
  let K := AdjoinRoot (rawCandidateModulus candidate)
  letI : Module.Finite (ZMod 2) K := by
    simpa [rawCandidateModulus] using hmod.1.finite_adjoinRoot
  funext t
  simp [rawTraceDetPayload, rawTraceDetTensor, encodeDenseInput,
    traceDeterminantTensor_apply]

/-- Finite comparison of the actual compatible array's decoded coefficients
with the coefficients calculated from the accepted field and coordinates. -/
noncomputable def rawTraceCompatibleCheck {s : Nat}
    (compatible : RawBinaryArray)
    (candidate : RawFieldCandidate s)
    (hfield : rawFieldCandidateCheck candidate = true)
    (forward inverse : RawCoordinateMatrix)
    (hcoordinates : rawCoordinateMatrixCheck (n := 3 * s) forward inverse = true) : Bool :=
  decide (∀ t : IncreasingTriple (3 * s),
    encodeDenseInput (decodeRawArray (n := 3 * s) compatible) t =
      rawTraceDetPayload candidate hfield forward inverse hcoordinates t)

theorem accepted_rawTraceCompatibleCheck {s : Nat}
    (compatible : RawBinaryArray)
    (candidate : RawFieldCandidate s)
    (hfield : rawFieldCandidateCheck candidate = true)
    (forward inverse : RawCoordinateMatrix)
    (hcoordinates : rawCoordinateMatrixCheck (n := 3 * s) forward inverse = true)
    (hcheck : rawTraceCompatibleCheck compatible candidate hfield forward inverse
      hcoordinates = true) :
    decodeRawArray (n := 3 * s) compatible =
      rawTraceDetTensor candidate hfield forward inverse hcoordinates := by
  apply binaryTensor_ext_of_increasing_coefficients
  · exact decodeRawArray_isAlternating (n := 3 * s) compatible
  · exact rawTraceDetTensor_alternating candidate hfield forward inverse hcoordinates
  · intro i j k hij hjk
    let t : IncreasingTriple (3 * s) := ⟨((i, j), k), ⟨hij, hjk⟩⟩
    have heq : ∀ t : IncreasingTriple (3 * s),
        encodeDenseInput (decodeRawArray (n := 3 * s) compatible) t =
          rawTraceDetPayload candidate hfield forward inverse hcoordinates t :=
      of_decide_eq_true (by simpa [rawTraceCompatibleCheck] using hcheck)
    have hc := heq t
    have hd := encode_decodeRawArray (n := 3 * s) compatible t
    have hp := congrFun (rawTraceDetPayload_eq_encode candidate hfield forward inverse
      hcoordinates) t
    change coefficient (decodeRawArray (n := 3 * s) compatible) i j k =
      coefficient (rawTraceDetTensor candidate hfield forward inverse hcoordinates) i j k
    have hleft : coefficient (decodeRawArray (n := 3 * s) compatible) i j k =
        encodeDenseInput (decodeRawArray (n := 3 * s) compatible) t := by
      simpa [t] using
        (encodeDenseInput_eq_semanticCoefficient
          (decodeRawArray (n := 3 * s) compatible) t).symm
    have hright : encodeDenseInput
        (rawTraceDetTensor candidate hfield forward inverse hcoordinates) t =
          coefficient (rawTraceDetTensor candidate hfield forward inverse hcoordinates) i j k := by
      simpa [t] using
        encodeDenseInput_eq_semanticCoefficient
          (rawTraceDetTensor candidate hfield forward inverse hcoordinates) t
    exact hleft.trans (hc.trans (hp.trans hright))

/-- S011 combined gate: the original raw decomposition verifier must accept,
and the compatible array must independently match the computed trace-field
coefficients. -/
noncomputable def rawTraceDecompositionCheck {s R : Nat}
    (p : RawDecomposition (3 * s) R)
    (candidate : RawFieldCandidate s)
    (hfield : rawFieldCandidateCheck candidate = true)
    (forward inverse : RawCoordinateMatrix)
    (hcoordinates : rawCoordinateMatrixCheck (n := 3 * s) forward inverse = true) : Bool :=
  rawDecompositionCheck p &&
    rawTraceCompatibleCheck p.compatible candidate hfield forward inverse hcoordinates

/-- An accepted combined gate proves the complete input identity with the
computed trace-determinant-compatible tensor and the explicitly factored
residual. It proves compatibility, not uniqueness or recovery completeness. -/
theorem accepted_rawTraceDecompositionCheck_sound {s R : Nat}
    (p : RawDecomposition (3 * s) R)
    (candidate : RawFieldCandidate s)
    (hfield : rawFieldCandidateCheck candidate = true)
    (forward inverse : RawCoordinateMatrix)
    (hcoordinates : rawCoordinateMatrixCheck (n := 3 * s) forward inverse = true)
    (hcheck : rawTraceDecompositionCheck p candidate hfield forward inverse
      hcoordinates = true) :
    ∀ x y z,
      decodeRawArray (n := 3 * s) p.input x y z =
        rawTraceDetTensor candidate hfield forward inverse hcoordinates x y z +
          pullback (decodeRawArray (n := p.supportDimension) p.residual)
            (rawSupportMap p.supportMatrix) x y z := by
  simp only [rawTraceDecompositionCheck, Bool.and_eq_true] at hcheck
  have hdecomp := accepted_rawDecompositionCheck_sound p hcheck.1
  have hclean := accepted_rawTraceCompatibleCheck p.compatible candidate hfield
    forward inverse hcoordinates hcheck.2
  have hsum : p.represented =
      rawTraceDetTensor candidate hfield forward inverse hcoordinates +
        pullback (decodeRawArray (n := p.supportDimension) p.residual)
          (rawSupportMap p.supportMatrix) := by
    rw [RawDecomposition.represented, hclean]
  intro x y z
  rw [hdecomp]
  exact congrArg (fun T : BinaryTensor (3 * s) => T x y z) hsum

end CorruptedFieldRecovery
