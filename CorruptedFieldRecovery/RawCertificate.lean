import CorruptedFieldRecovery.DenseInput
import Mathlib.Tactic.Linarith

/-! Raw array boundary for alternating dense tensors.

The array is indexed by the row-major ordered coefficient offset used by
`ExecutableCertificate`. Decoding selects only increasing triples and expands
them in the six-term minor basis. Thus the output is alternating by
construction. This file certifies the array comparison boundary; it does not
certify that the compatible array encodes a field determinant or that the
residual has bounded support.
-/

namespace CorruptedFieldRecovery

abbrev RawCoefficientArray := Array (ZMod 2)

def rawCoefficientOffset (n : Nat) (i j k : Fin n) : Nat :=
  (i.val * n + j.val) * n + k.val

/-- The raw dense array decodes to the finite sum of its selected minor
coefficients. This is a computable finite sum through `decodeDenseInput`. -/
def decodeRawArray {n : Nat} (raw : RawCoefficientArray) : BinaryTensor n :=
  decodeDenseInput (fun t =>
    raw[rawCoefficientOffset n (increasingTripleI t)
      (increasingTripleJ t) (increasingTripleK t)]!)

/-- Decoder identity at every serialized increasing-triple coordinate. -/
theorem encode_decodeRawArray {n : Nat} (raw : RawCoefficientArray)
    (t : IncreasingTriple n) :
    encodeDenseInput (decodeRawArray (n := n) raw) t =
      raw[rawCoefficientOffset n (increasingTripleI t)
        (increasingTripleJ t) (increasingTripleK t)]! := by
  exact congrFun (encode_decodeDenseInput (n := n) _) t

theorem decodeRawArray_isAlternating {n : Nat} (raw : RawCoefficientArray) :
    IsAlternating (decodeRawArray (n := n) raw) :=
  decodeDenseInput_isAlternating _

/-- Agreement of raw arrays implies equality of the decoded alternating
tensors. This theorem needs no semantic tensor field attached to either input. -/
theorem decodeRawArray_congr {n : Nat} {left right : RawCoefficientArray}
    (h : left = right) :
    decodeRawArray (n := n) left = decodeRawArray (n := n) right := by
  subst right
  rfl

/-- Accepted raw comparison: both serialized arrays have exactly `n^3`
entries and all bits agree. -/
def rawArrayCheck {n : Nat} (input represented : RawCoefficientArray) : Bool :=
  decide (input.size = n * n * n) &&
    decide (represented.size = n * n * n) && input == represented

theorem accepted_raw_array_decoders_equal {n : Nat}
    (input represented : RawCoefficientArray)
    (accepted : rawArrayCheck (n := n) input represented = true) :
    decodeRawArray (n := n) input = decodeRawArray (n := n) represented := by
  simp only [rawArrayCheck, Bool.and_eq_true] at accepted
  have hEq : (input == represented) = true := accepted.2
  exact decodeRawArray_congr (eq_of_beq hEq)

/-- Compute the coefficientwise sum in the serialized representation. -/
def rawArrayAdd (left right : RawCoefficientArray) : RawCoefficientArray :=
  left.mapIdx (fun i x => x + right[i]!)

theorem rawArrayAdd_get! (left right : RawCoefficientArray) (i : Nat)
    (hi : i < left.size) :
    (rawArrayAdd left right)[i]! = left[i]! + right[i]! := by
  simp [rawArrayAdd, hi]

/-- Decoding the computed coefficientwise sum agrees with addition of the
decoded tensors. The size hypothesis makes every accessed offset an entry of
the dense arrays. -/
theorem decodeRawArray_add {n : Nat} (left right : RawCoefficientArray)
    (hsize : left.size = n * n * n) :
    decodeRawArray (n := n) (rawArrayAdd left right) =
      decodeRawArray (n := n) left + decodeRawArray (n := n) right := by
  apply binaryTensor_ext_of_increasing_coefficients
  · exact decodeRawArray_isAlternating (n := n) _
  · have hl := decodeRawArray_isAlternating (n := n) left
    have hr := decodeRawArray_isAlternating (n := n) right
    refine ⟨?_, ?_, ?_⟩
    · intro x z
      simp [hl.1 x z, hr.1 x z]
    · intro x y
      simp [hl.2.1 x y, hr.2.1 x y]
    · intro x y
      simp [hl.2.2 x y, hr.2.2 x y]
  · intro i j k hij hjk
    let t : IncreasingTriple n := ⟨((i, j), k), ⟨hij, hjk⟩⟩
    have hoff : rawCoefficientOffset n i j k < left.size := by
      rw [hsize]
      have hi : i.val < n := i.isLt
      have hj : j.val < n := j.isLt
      have hk : k.val < n := k.isLt
      have hi' : i.val + 1 ≤ n := Nat.succ_le_of_lt hi
      have hj' : j.val + 1 ≤ n := Nat.succ_le_of_lt hj
      have hrow : i.val * n + j.val + 1 ≤ n * n := by
        have hm := Nat.mul_le_mul_right n hi'
        nlinarith
      change (i.val * n + j.val) * n + k.val < n * n * n
      calc
        (i.val * n + j.val) * n + k.val <
            (i.val * n + j.val + 1) * n := by nlinarith
        _ ≤ (n * n) * n := Nat.mul_le_mul_right n hrow
        _ = n * n * n := by ring
    have hsum := rawArrayAdd_get! left right
      (rawCoefficientOffset n i j k) hoff
    change coefficient (decodeRawArray (n := n) (rawArrayAdd left right)) i j k =
      coefficient (decodeRawArray (n := n) left + decodeRawArray (n := n) right) i j k
    have hcomputed :
        coefficient (decodeRawArray (n := n) (rawArrayAdd left right)) i j k =
          (rawArrayAdd left right)[rawCoefficientOffset n i j k]! := by
      simpa [coefficient, encodeDenseInput, coordinateVectorCode_eq_coordinateVector, t] using
        (encode_decodeRawArray (n := n) (rawArrayAdd left right) t)
    have hleft : coefficient (decodeRawArray (n := n) left) i j k =
        left[rawCoefficientOffset n i j k]! := by
      simpa [coefficient, encodeDenseInput, coordinateVectorCode_eq_coordinateVector, t] using
        (encode_decodeRawArray (n := n) left t)
    have hright : coefficient (decodeRawArray (n := n) right) i j k =
        right[rawCoefficientOffset n i j k]! := by
      simpa [coefficient, encodeDenseInput, coordinateVectorCode_eq_coordinateVector, t] using
        (encode_decodeRawArray (n := n) right t)
    rw [hcomputed, hsum, ← hleft, ← hright]
    simp [coefficient]

/-- The certificate gate checks that the advertised represented array is the
computed compatible-plus-residual array and that all arrays have dense size. -/
def rawCertificateCheck {n : Nat} (compatible residual represented : RawCoefficientArray) : Bool :=
  decide (compatible.size = n * n * n) &&
    decide (residual.size = n * n * n) &&
    decide (represented.size = n * n * n) &&
    (represented == rawArrayAdd compatible residual)

theorem accepted_raw_certificate_is_computed_sum {n : Nat}
    (compatible residual represented : RawCoefficientArray)
    (accepted : rawCertificateCheck (n := n) compatible residual represented = true) :
    represented = rawArrayAdd compatible residual := by
  simp only [rawCertificateCheck, Bool.and_eq_true] at accepted
  exact eq_of_beq accepted.2

end CorruptedFieldRecovery
