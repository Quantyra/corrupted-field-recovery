import CorruptedFieldRecovery.RawCertificate
import CorruptedFieldRecovery.Support

/-! Raw-only compatible-plus-residual certificate verification.

The payload contains arrays, not semantic tensors or proof fields. The input,
compatible tensor, and quotient residual are decoded from their arrays. A raw
binary matrix supplies the support map. The verifier checks exact increasing
coefficients of the reconstructed sum, so acceptance determines the tensor on
all vectors by alternating extensionality. This module does not recognize a
trace-determinant field structure; it verifies the algebraic compatible-plus-
supported decomposition represented by the payload.
-/

namespace CorruptedFieldRecovery

abbrev RawBinaryArray := Array (ZMod 2)

/-- Row-major offset for an `n` by `d` support matrix. -/
def rawSupportOffset {n d : Nat} (i : Fin n) (j : Fin d) : Nat :=
  i.val * d + j.val

/-- The raw support matrix interpreted as a linear observation map. -/
def rawSupportMap {n d : Nat} (matrix : RawBinaryArray) :
    BinaryVector n →ₗ[ZMod 2] BinaryVector d := by
  classical
  let f : BinaryVector n → BinaryVector d := fun x j =>
    ∑ i : Fin n, matrix[rawSupportOffset (d := d) i j]! * x i
  refine { toFun := f, map_add' := ?_, map_smul' := ?_ }
  · intro x y
    ext j
    simp [f, Finset.sum_add_distrib, mul_add]
  · intro c x
    ext j
    simp [f, Finset.mul_sum, mul_assoc, mul_comm]

/-- A payload consisting only of serialized finite arrays. -/
structure RawDecomposition (n R : Nat) where
  supportDimension : Nat
  input : RawBinaryArray
  compatible : RawBinaryArray
  residual : RawBinaryArray
  supportMatrix : RawBinaryArray

/-- Decode the two alternating tensors and pull the residual back along the
serialized support map. The residual therefore factors through exactly the
advertised `supportDimension` coordinates by construction. -/
def RawDecomposition.represented {n R : Nat} (p : RawDecomposition n R) :
    BinaryTensor n :=
  decodeRawArray (n := n) p.compatible +
    pullback (decodeRawArray (n := p.supportDimension) p.residual)
      (rawSupportMap p.supportMatrix)

/-- Executable comparison of the serialized increasing coefficients. The
encoder uses explicit coordinate vectors, so this does not depend on the
noncomputable basis-based `coefficient` abbreviation. -/
def rawIncreasingCoefficientCheck {n : Nat}
    (input represented : BinaryTensor n) : Bool :=
  decide (∀ t : IncreasingTriple n,
    encodeDenseInput input t = encodeDenseInput represented t)

theorem RawDecomposition.represented_alternating {n R : Nat}
    (p : RawDecomposition n R) : IsAlternating p.represented := by
  let A := decodeRawArray (n := n) p.compatible
  let E := decodeRawArray (n := p.supportDimension) p.residual
  let u : BinaryVector n →ₗ[ZMod 2] BinaryVector p.supportDimension :=
    rawSupportMap (n := n) (d := p.supportDimension) p.supportMatrix
  have hA := decodeRawArray_isAlternating (n := n) p.compatible
  have hE := decodeRawArray_isAlternating (n := p.supportDimension) p.residual
  change IsAlternating (A + pullback E u)
  constructor
  · intro x y
    change A x x y + E (u x) (u x) (u y) = 0
    rw [hA.1 x y, hE.1 (u x) (u y)]
    simp
  constructor
  · intro x y
    change A x y x + E (u x) (u y) (u x) = 0
    rw [hA.2.1 x y, hE.2.1 (u x) (u y)]
    simp
  · intro x y
    change A x y y + E (u x) (u y) (u y) = 0
    rw [hA.2.2 x y, hE.2.2 (u x) (u y)]
    simp

/-- Boolean raw verifier. It checks the actual array dimensions and the exact
finite increasing coefficients of input and reconstructed representation.
The support bound is the dimension of the explicitly serialized quotient map.
-/
def rawDecompositionCheck {n R : Nat} (p : RawDecomposition n R) : Bool :=
  decide (p.supportDimension ≤ R) &&
    decide (p.input.size = n * n * n) &&
    decide (p.compatible.size = n * n * n) &&
    decide (p.residual.size = p.supportDimension * p.supportDimension * p.supportDimension) &&
    decide (p.supportMatrix.size = n * p.supportDimension) &&
    rawIncreasingCoefficientCheck (decodeRawArray (n := n) p.input) p.represented

theorem accepted_rawDecompositionCheck_support_bound {n R : Nat}
    (p : RawDecomposition n R)
    (h : rawDecompositionCheck p = true) : p.supportDimension ≤ R := by
  simp only [rawDecompositionCheck, rawIncreasingCoefficientCheck,
    Bool.and_eq_true] at h
  exact of_decide_eq_true h.1.1.1.1.1

/-- Acceptance proves exact equality of the decoded input and the reconstructed
compatible-plus-residual tensor on every physical vector. No semantic tensor,
field structure, bridge equation, or conclusion is stored in the payload. -/
theorem accepted_rawDecompositionCheck_sound {n R : Nat}
    (p : RawDecomposition n R)
    (h : rawDecompositionCheck p = true) :
    ∀ x y z, decodeRawArray (n := n) p.input x y z = p.represented x y z := by
  classical
  simp only [rawDecompositionCheck, rawIncreasingCoefficientCheck,
    Bool.and_eq_true] at h
  have hencoded : ∀ t : IncreasingTriple n,
      encodeDenseInput (decodeRawArray (n := n) p.input) t =
        encodeDenseInput p.represented t :=
    of_decide_eq_true h.2
  have hcoeff : ∀ i j k : Fin n, i < j → j < k →
      coefficient (decodeRawArray (n := n) p.input) i j k =
        coefficient p.represented i j k := by
    intro i j k hij hjk
    let t : IncreasingTriple n := ⟨((i, j), k), ⟨hij, hjk⟩⟩
    have ht := hencoded t
    simpa [t, encodeDenseInput_eq_semanticCoefficient] using ht
  have hin := decodeRawArray_isAlternating (n := n) p.input
  have hrep := p.represented_alternating
  have htensor := binaryTensor_ext_of_increasing_coefficients hin hrep hcoeff
  intro x y z
  exact congrArg (fun T : BinaryTensor n => T x y z) htensor

/-- The accepted residual has an explicit common-support factorization through
the raw matrix map, whose codomain dimension is the checked value `d`. -/
theorem rawDecomposition_residual_factors {n R : Nat}
    (p : RawDecomposition n R) (x y z : BinaryVector n) :
    pullback (decodeRawArray (n := p.supportDimension) p.residual)
      (rawSupportMap p.supportMatrix) x y z =
      decodeRawArray (n := p.supportDimension) p.residual
        (rawSupportMap p.supportMatrix x)
        (rawSupportMap p.supportMatrix y)
        (rawSupportMap p.supportMatrix z) := by
  rfl

/-- The residual's complete mode image is contained in the dual image of its
serialized support map. Thus it has a common support of dimension at most the
map's `d`-dimensional codomain (and not merely a claimed support label). -/
theorem modeImage_pullback_le_dualMap_range {n d : Nat}
    (E : BinaryTensor d) (u : BinaryVector n →ₗ[ZMod 2] BinaryVector d) :
    modeImage (pullback E u) ≤ LinearMap.range u.dualMap := by
  apply Submodule.span_le.mpr
  rintro ψ ⟨⟨x, y⟩, rfl⟩
  refine ⟨E (u x) (u y), ?_⟩
  ext z
  simp [LinearMap.dualMap_apply]

end CorruptedFieldRecovery
