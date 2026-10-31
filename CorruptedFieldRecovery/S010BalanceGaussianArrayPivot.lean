import CorruptedFieldRecovery.S010BalanceGaussianArrayExecution

open scoped Matrix

namespace CorruptedFieldRecovery

/-- One executable Gauss-Jordan row update on a rectangular nested array.
The output is rebuilt in row-major `Fin` order, and each updated cell reads
only the pre-update array. -/
def actualBalanceGaussianArrayPivotRow {m n : Nat}
    (cells : Array (Array (ZMod 2))) (pivotRow : Fin m)
    (pivotColumn : Fin n) : Array (Array (ZMod 2)) :=
  Array.ofFn fun row : Fin m =>
    Array.ofFn fun col : Fin n =>
      if row = pivotRow then
        actualBalanceGaussianArrayView cells row col
      else
        actualBalanceGaussianArrayView cells row col +
          actualBalanceGaussianArrayView cells row pivotColumn *
            actualBalanceGaussianArrayView cells pivotRow col

/-- The nested-array row update commutes exactly with the accepted matrix row
update when the array is read through the total finite matrix view. -/
theorem actualBalanceGaussianArrayPivotRow_view_eq {m n : Nat}
    (cells : Array (Array (ZMod 2))) (pivotRow : Fin m)
    (pivotColumn : Fin n) :
    actualBalanceGaussianArrayView
        (actualBalanceGaussianArrayPivotRow cells pivotRow pivotColumn) =
      balanceGaussianPivotRow (actualBalanceGaussianArrayView cells)
        pivotRow pivotColumn := by
  ext row col
  simp [actualBalanceGaussianArrayPivotRow, actualBalanceGaussianArrayView,
    balanceGaussianPivotRow]

/-- Execute a supplied sequence of pivot updates directly on the nested-array
representation. This is the update primitive's finite-array sequence; pivot
selection and runtime accounting are separate obligations. -/
def actualBalanceGaussianArrayPivotSequence {m n : Nat}
    (cells : Array (Array (ZMod 2))) :
    List (Fin m × Fin n) → Array (Array (ZMod 2))
  | [] => cells
  | (pivotRow, pivotColumn) :: steps =>
      actualBalanceGaussianArrayPivotSequence
        (actualBalanceGaussianArrayPivotRow cells pivotRow pivotColumn) steps

/-- Array pivot sequences refine the existing mathematical row-operation
sequence exactly, for every supplied pivot transcript. -/
theorem actualBalanceGaussianArrayPivotSequence_view_eq {m n : Nat}
    (cells : Array (Array (ZMod 2))) (steps : List (Fin m × Fin n)) :
    actualBalanceGaussianArrayView
        (actualBalanceGaussianArrayPivotSequence cells steps) =
      balanceGaussianPivotSequence (actualBalanceGaussianArrayView cells) steps := by
  induction steps generalizing cells with
  | nil => rfl
  | cons step steps ih =>
      rcases step with ⟨pivotRow, pivotColumn⟩
      change actualBalanceGaussianArrayView
          (actualBalanceGaussianArrayPivotSequence
            (actualBalanceGaussianArrayPivotRow cells pivotRow pivotColumn)
            steps) =
        balanceGaussianPivotSequence
          (balanceGaussianPivotRow
            (actualBalanceGaussianArrayView cells) pivotRow pivotColumn) steps
      rw [ih]
      rw [actualBalanceGaussianArrayPivotRow_view_eq]

/-- The array-backed update sequence preserves the original matrix kernel,
using the already proved invariance of the corresponding matrix operations. -/
theorem actualBalanceGaussianArrayPivotSequence_kernel_iff {m n : Nat}
    [Fintype (Fin n)] (cells : Array (Array (ZMod 2)))
    (steps : List (Fin m × Fin n)) (x : Fin n → ZMod 2) :
    actualBalanceGaussianArrayView (m := m) (n := n)
        (actualBalanceGaussianArrayPivotSequence cells steps) *ᵥ x = 0 ↔
      actualBalanceGaussianArrayView (m := m) (n := n) cells *ᵥ x = 0 := by
  rw [actualBalanceGaussianArrayPivotSequence_view_eq]
  exact balanceGaussianPivotSequence_kernel_iff steps
    (actualBalanceGaussianArrayView (m := m) (n := n) cells) x

/-- On the serialized raw balance matrix, one array-backed pivot update
refines exactly the accepted Gaussian matrix operation. -/
theorem actualBalanceGaussianSerializedArrayPivotRow_refines {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s)
    (pivotRow : Fin (4 * ((3 * s) * (3 * s))))
    (pivotColumn : Fin ((3 * s) * (3 * s))) :
    actualBalanceGaussianArrayView
        (actualBalanceGaussianArrayPivotRow
          (actualBalanceSerializedCoefficientMatrix
            (decodeRawArray (n := 3 * s) raw) tape)
          pivotRow pivotColumn) =
      balanceGaussianPivotRow (actualBalanceGaussianRawMatrix raw tape)
        pivotRow pivotColumn := by
  rw [actualBalanceGaussianArrayPivotRow_view_eq,
    actualBalanceGaussianSerializedArrayView_eq_rawMatrix]

end CorruptedFieldRecovery
