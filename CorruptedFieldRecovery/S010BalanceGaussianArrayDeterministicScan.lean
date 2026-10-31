import CorruptedFieldRecovery.S010BalanceGaussianArrayPivot

open scoped Matrix

namespace CorruptedFieldRecovery

/-- Select the first unused pivot row by enumerating rows in `Fin` order and
reading the selected column directly from the nested-array view. The mask
condition matches the accepted matrix selector exactly. -/
def actualBalanceGaussianArrayFirstUnusedPivotRow {m n : Nat}
    (cells : Array (Array (ZMod 2))) (column : Fin n)
    (used : Finset (Fin m)) : Option (Fin m) :=
  (List.ofFn fun row : Fin m => row).find? fun row =>
    decide ((if row ∈ used then 0 else
      actualBalanceGaussianArrayView cells row column) = 1)

/-- Array pivot selection returns precisely the accepted deterministic
first-unused-row result on the array's matrix view. -/
theorem actualBalanceGaussianArrayFirstUnusedPivotRow_eq
    {m n : Nat} (cells : Array (Array (ZMod 2))) (column : Fin n)
    (used : Finset (Fin m)) :
    actualBalanceGaussianArrayFirstUnusedPivotRow cells column used =
      balanceFirstUnusedPivotRow (actualBalanceGaussianArrayView cells)
        column used := by
  rfl

/-- Deterministically process the listed columns using array-backed pivot
selection and nested-array row updates. The returned list records the actual
row/column operations in execution order. -/
def actualBalanceGaussianArrayColumnScan {m n : Nat}
    (cells : Array (Array (ZMod 2))) : Finset (Fin m) → List (Fin n) →
      Array (Array (ZMod 2)) × List (Fin m × Fin n)
  | _used, [] => (cells, [])
  | used, column :: columns =>
      match actualBalanceGaussianArrayFirstUnusedPivotRow cells column used with
      | none => actualBalanceGaussianArrayColumnScan cells used columns
      | some row =>
          let rest := actualBalanceGaussianArrayColumnScan
            (actualBalanceGaussianArrayPivotRow cells row column)
            (insert row used) columns
          (rest.1, (row, column) :: rest.2)

/-- The array scan's final view and pivot transcript agree with the accepted
matrix scan. This is proved by induction on the supplied column order, using
the exact one-step selector and row-update refinement theorems. -/
theorem actualBalanceGaussianArrayColumnScan_refines
    {m n : Nat} (cells : Array (Array (ZMod 2))) (used : Finset (Fin m))
    (columns : List (Fin n)) :
    (actualBalanceGaussianArrayView
        (actualBalanceGaussianArrayColumnScan cells used columns).1,
      (actualBalanceGaussianArrayColumnScan cells used columns).2) =
      balanceGaussianColumnScan (actualBalanceGaussianArrayView cells)
        used columns := by
  induction columns generalizing cells used with
  | nil => rfl
  | cons column columns ih =>
      cases hpivot : actualBalanceGaussianArrayFirstUnusedPivotRow
          cells column used with
      | none =>
          have hpivot' :
              balanceFirstUnusedPivotRow
                (actualBalanceGaussianArrayView cells) column used = none := by
            rw [← actualBalanceGaussianArrayFirstUnusedPivotRow_eq, hpivot]
          simpa [actualBalanceGaussianArrayColumnScan,
            balanceGaussianColumnScan, hpivot, hpivot'] using
              ih cells used
      | some row =>
          have hpivot' :
              balanceFirstUnusedPivotRow
                (actualBalanceGaussianArrayView cells) column used = some row := by
            rw [← actualBalanceGaussianArrayFirstUnusedPivotRow_eq, hpivot]
          simpa [actualBalanceGaussianArrayColumnScan,
            balanceGaussianColumnScan, hpivot, hpivot',
            actualBalanceGaussianArrayPivotRow_view_eq] using
              congrArg (fun result => (result.1, (row, column) :: result.2))
                (ih (actualBalanceGaussianArrayPivotRow cells row column)
                  (insert row used))

/-- Run the deterministic nested-array scan on the serialized raw balance
coefficient matrix. The input hypotheses are exactly those of the serializer;
this definition adds no pivot transcript as an input. -/
def actualBalanceGaussianSerializedArrayDeterministicScan {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s) :=
  actualBalanceGaussianArrayColumnScan
    (m := 4 * ((3 * s) * (3 * s)))
    (n := (3 * s) * (3 * s))
    (actualBalanceSerializedCoefficientMatrix
      (decodeRawArray (n := 3 * s) raw) tape)
    ∅ (List.ofFn fun column : Fin ((3 * s) * (3 * s)) => column)

/-- The array-driven deterministic scan returns the same reduced matrix view
and ordered pivot transcript as the accepted scan on the raw physical balance
matrix. -/
theorem actualBalanceGaussianSerializedArrayDeterministicScan_refines
    {s : Nat} (raw : RawCoefficientArray) (tape : FiveWordTape s) :
    (actualBalanceGaussianArrayView
        (m := 4 * ((3 * s) * (3 * s)))
        (n := (3 * s) * (3 * s))
        (actualBalanceGaussianSerializedArrayDeterministicScan raw tape).1,
      (actualBalanceGaussianSerializedArrayDeterministicScan raw tape).2) =
      actualBalanceGaussianRawScan raw tape := by
  rw [actualBalanceGaussianSerializedArrayDeterministicScan,
    actualBalanceGaussianArrayColumnScan_refines,
    actualBalanceGaussianSerializedArrayView_eq_rawMatrix,
    actualBalanceGaussianRawScan]

/-- The final array view has the same homogeneous solution set as the original
raw balance matrix. This follows from the scan refinement and the accepted
kernel-preservation proof for the matrix scan. -/
theorem actualBalanceGaussianSerializedArrayDeterministicScan_kernel_iff
    {s : Nat} (raw : RawCoefficientArray) (tape : FiveWordTape s)
    (x : Fin ((3 * s) * (3 * s)) → ZMod 2) :
    actualBalanceGaussianArrayView
        (m := 4 * ((3 * s) * (3 * s)))
        (n := (3 * s) * (3 * s))
        (actualBalanceGaussianSerializedArrayDeterministicScan raw tape).1 *ᵥ x = 0 ↔
      actualBalanceGaussianRawMatrix raw tape *ᵥ x = 0 := by
  have hpair := actualBalanceGaussianSerializedArrayDeterministicScan_refines
    raw tape
  have hmatrix :
      actualBalanceGaussianArrayView
          (m := 4 * ((3 * s) * (3 * s)))
          (n := (3 * s) * (3 * s))
          (actualBalanceGaussianSerializedArrayDeterministicScan raw tape).1 =
        (actualBalanceGaussianRawScan raw tape).1 := by
    have hfst := congrArg Prod.fst hpair
    simpa using hfst
  rw [hmatrix]
  exact balanceGaussianColumnScan_kernel_iff
    (List.ofFn fun column : Fin ((3 * s) * (3 * s)) => column)
    (actualBalanceGaussianRawMatrix raw tape) ∅ x

end CorruptedFieldRecovery
