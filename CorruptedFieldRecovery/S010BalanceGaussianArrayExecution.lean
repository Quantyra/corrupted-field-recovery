import CorruptedFieldRecovery.S010BalanceGaussianIndexLayoutBridge
import CorruptedFieldRecovery.S010BalanceGaussianRawKernelBasis

open scoped Matrix

namespace CorruptedFieldRecovery

/-- Read an already serialized rectangular coefficient array as a finite
matrix. Missing cells default to zero, but the canonical balance serializer
is proved below to have every requested cell present. -/
def actualBalanceGaussianArrayView {m n : Nat}
    (cells : Array (Array (ZMod 2))) : Matrix (Fin m) (Fin n) (ZMod 2) :=
  fun row col =>
    ((cells[row.val]?.bind fun entries => entries[col.val]?).getD 0)

/-- The matrix view of the serialized physical balance coefficients is exactly
the matrix used to specify the Gaussian solver. The equality follows from the
row/column list-position bridge, not from recomputing coefficient formulas. -/
theorem actualBalanceGaussianSerializedArrayView_eq_rawMatrix {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s) :
    actualBalanceGaussianArrayView
      (actualBalanceSerializedCoefficientMatrix
        (decodeRawArray (n := 3 * s) raw) tape) =
      actualBalanceGaussianRawMatrix raw tape := by
  ext row col
  have hcell := actualBalanceGaussianSerializedCell_eq_rawMatrix raw tape row col
  change ((actualBalanceSerializedCoefficientMatrix
      (decodeRawArray (n := 3 * s) raw) tape)[row.val]?.bind
    fun entries => entries[col.val]?).getD 0 = _
  rw [hcell]
  rfl

/-- Run the deterministic binary column scan by reading coefficients from the
serialized nested array through the finite matrix view. -/
def actualBalanceGaussianSerializedArrayScan {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s) :=
  let A : Matrix (Fin (4 * ((3 * s) * (3 * s))))
      (Fin ((3 * s) * (3 * s))) (ZMod 2) :=
    actualBalanceGaussianArrayView
      (m := 4 * ((3 * s) * (3 * s)))
      (n := (3 * s) * (3 * s))
      (actualBalanceSerializedCoefficientMatrix
        (decodeRawArray (n := 3 * s) raw) tape)
  balanceGaussianColumnScan A ∅
    (List.ofFn fun col : Fin ((3 * s) * (3 * s)) => col)

/-- The array-backed execution has exactly the same reduced matrix and ordered
pivot transcript as the raw mathematical matrix scan. -/
theorem actualBalanceGaussianSerializedArrayScan_eq_rawScan {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s) :
    actualBalanceGaussianSerializedArrayScan raw tape =
      actualBalanceGaussianRawScan raw tape := by
  rw [actualBalanceGaussianSerializedArrayScan,
    actualBalanceGaussianSerializedArrayView_eq_rawMatrix,
    actualBalanceGaussianRawScan]

/-- The serialized-array scan's free-column candidates reconstruct every
solution of its own reduced system, by transport from the raw matrix scan. -/
theorem actualBalanceGaussianSerializedArrayScan_reconstruct {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s) :
    ∀ x : Fin ((3 * s) * (3 * s)) → ZMod 2,
      (actualBalanceGaussianSerializedArrayScan raw tape).1 *ᵥ x = 0 →
      x = ∑ free : balanceGaussianFreeIndex
          (actualBalanceGaussianSerializedArrayScan raw tape).2,
        x free.1 • balanceGaussianFreeCandidateFamily
          (actualBalanceGaussianSerializedArrayScan raw tape).1
          (actualBalanceGaussianSerializedArrayScan raw tape).2 free := by
  rw [actualBalanceGaussianSerializedArrayScan_eq_rawScan]
  exact actualBalanceGaussianRawScan_reconstruct raw tape

/-- Every candidate in the serialized-array scan decodes to an endomorphism
that satisfies the actual physical balance equations. -/
theorem actualBalanceGaussianSerializedArrayCandidate_balanced {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s)
    (free : balanceGaussianFreeIndex
      (actualBalanceGaussianSerializedArrayScan raw tape).2) :
    actualFourBilinearBalanced (decodeRawArray (n := 3 * s) raw) tape
      (actualBalanceGaussianEndFromCoordinates
        (balanceGaussianFreeKernelCandidate
          (actualBalanceGaussianSerializedArrayScan raw tape).1
            (actualBalanceGaussianSerializedArrayScan raw tape).2 free.1)) := by
  rcases free with ⟨column, hfree⟩
  let freeRaw : balanceGaussianFreeIndex
      (actualBalanceGaussianRawScan raw tape).2 :=
    ⟨column, by
      simpa only [actualBalanceGaussianSerializedArrayScan_eq_rawScan] using hfree⟩
  simpa [actualBalanceGaussianSerializedArrayScan_eq_rawScan, freeRaw] using
    actualBalanceGaussianRawCandidate_balanced raw tape freeRaw

/-- With the declared raw size, every serialized-array free-column candidate
is accepted by the finite physical balance checker. -/
theorem actualBalanceGaussianSerializedArrayCandidate_check_true {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s)
    (hsize : raw.size = (3 * s) * (3 * s) * (3 * s))
    (free : balanceGaussianFreeIndex
      (actualBalanceGaussianSerializedArrayScan raw tape).2) :
    actualBalanceRawInputConstraintCheck raw tape
      (actualBalanceGaussianEndFromCoordinates
        (balanceGaussianFreeKernelCandidate
          (actualBalanceGaussianSerializedArrayScan raw tape).1
            (actualBalanceGaussianSerializedArrayScan raw tape).2 free.1)) = true := by
  rcases free with ⟨column, hfree⟩
  let freeRaw : balanceGaussianFreeIndex
      (actualBalanceGaussianRawScan raw tape).2 :=
    ⟨column, by
      simpa only [actualBalanceGaussianSerializedArrayScan_eq_rawScan] using hfree⟩
  simpa [actualBalanceGaussianSerializedArrayScan_eq_rawScan, freeRaw] using
    actualBalanceGaussianRawCandidate_checker_true raw tape hsize freeRaw

end CorruptedFieldRecovery
