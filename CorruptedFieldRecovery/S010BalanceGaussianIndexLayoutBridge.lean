import CorruptedFieldRecovery.S010BalanceGaussianRawSolverBridge
import CorruptedFieldRecovery.S010BalanceRawInputLayout
import Mathlib.Logic.Equiv.Fin.Basic

namespace CorruptedFieldRecovery

/-- Row-major enumeration of a product Fin type agrees with the inverse
`finProdFinEquiv` order, after mapping each pair through any function. This
isolates the only arithmetic fact needed by the serializer layout proof. -/
private theorem list_ofFn_finProdFinEquiv_symm_map {m n : Nat} {β : Type}
    (f : Fin m × Fin n → β) :
    List.ofFn (fun k : Fin (m * n) =>
      f ((finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)).symm k)) =
      (List.ofFn fun i : Fin m => i).flatMap fun i =>
        (List.ofFn fun j : Fin n => j).map fun j => f (i, j) := by
  rw [List.ofFn_mul]
  simp only [List.flatMap]
  apply congrArg List.flatten
  rw [← List.ofFn_comp']
  rw [List.ofFn_inj]
  funext i
  rw [← List.ofFn_comp']
  rw [List.ofFn_inj]
  funext j
  apply congrArg f
  let index : Fin (m * n) := ⟨i.val * n + j.val, by
    calc
      i.val * n + j.val < i.val * n + n := Nat.add_lt_add_left j.isLt _
      _ = (i.val + 1) * n := by ring
      _ ≤ m * n := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)⟩
  have hindex : index = (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)) (i, j) := by
    apply Fin.ext
    change i.val * n + j.val = j.val + n * i.val
    ring
  change ((finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)).symm index) = (i, j)
  calc
    (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)).symm index =
        (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)).symm
          ((finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)) (i, j)) :=
      congrArg (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)).symm hindex
    _ = (i, j) := Equiv.symm_apply_apply _ _

/-- The row-list order is exactly the inverse image of increasing finite row
indices under the Gaussian row equivalence. The product flattening is
slot-major, then first coordinate, then second coordinate. -/
theorem actualBalanceGaussianRowList_eq_ofFn_symm (s : Nat) :
    actualBalanceRowList s =
      List.ofFn (fun row : Fin (4 * ((3 * s) * (3 * s))) =>
        (actualBalanceGaussianRowEquiv s).symm row) := by
  have hinner : actualBalanceColumnList s =
      List.ofFn (fun col : Fin ((3 * s) * (3 * s)) =>
        (actualBalanceGaussianColumnEquiv s).symm col) := by
    simpa [actualBalanceColumnList, actualBalanceCoordinateList,
      actualBalanceGaussianColumnEquiv] using
        (list_ofFn_finProdFinEquiv_symm_map
          (m := 3 * s) (n := 3 * s)
          (f := fun pair : Fin (3 * s) × Fin (3 * s) => pair)).symm
  calc
    actualBalanceRowList s =
        (List.ofFn fun i : Fin 4 => i).flatMap fun i =>
          (actualBalanceColumnList s).map fun pair => (i, pair.1, pair.2) := by
      simp [actualBalanceRowList, actualBalanceColumnList,
        actualBalanceCoordinateList, List.map_flatMap, Function.comp_def]
    _ = (List.ofFn fun i : Fin 4 => i).flatMap fun i =>
          (List.ofFn fun col : Fin ((3 * s) * (3 * s)) =>
            (actualBalanceGaussianColumnEquiv s).symm col).map
              fun pair => (i, pair.1, pair.2) := by
      rw [hinner]
    _ = List.ofFn (fun row : Fin (4 * ((3 * s) * (3 * s))) =>
          (actualBalanceGaussianRowEquiv s).symm row) := by
      simpa [actualBalanceGaussianRowEquiv, actualBalanceGaussianColumnEquiv] using
        (list_ofFn_finProdFinEquiv_symm_map
          (m := 4) (n := (3 * s) * (3 * s))
          (f := fun pair : Fin 4 × Fin ((3 * s) * (3 * s)) =>
            (pair.1, (actualBalanceGaussianColumnEquiv s).symm pair.2))).symm

/-- The column-list order is exactly the inverse image of increasing finite
column indices under the Gaussian column equivalence: first matrix row, then
matrix column. -/
theorem actualBalanceGaussianColumnList_eq_ofFn_symm (s : Nat) :
    actualBalanceColumnList s =
      List.ofFn (fun col : Fin ((3 * s) * (3 * s)) =>
        (actualBalanceGaussianColumnEquiv s).symm col) := by
  simpa [actualBalanceColumnList, actualBalanceCoordinateList,
    actualBalanceGaussianColumnEquiv] using
      (list_ofFn_finProdFinEquiv_symm_map
        (m := 3 * s) (n := 3 * s)
        (f := fun pair : Fin (3 * s) × Fin (3 * s) => pair)).symm

/-- Looking up a finite row index in the serialized row order returns the
corresponding physical four-slot row. -/
theorem actualBalanceGaussianRowList_getElem?_equiv (s : Nat)
    (row : Fin (4 * ((3 * s) * (3 * s)))) :
    (actualBalanceRowList s)[row.val]? =
      some ((actualBalanceGaussianRowEquiv s).symm row) := by
  rw [actualBalanceGaussianRowList_eq_ofFn_symm]
  simp

/-- Looking up a finite column index in the serialized column order returns
the corresponding matrix-entry coordinate pair. -/
theorem actualBalanceGaussianColumnList_getElem?_equiv (s : Nat)
    (col : Fin ((3 * s) * (3 * s))) :
    (actualBalanceColumnList s)[col.val]? =
      some ((actualBalanceGaussianColumnEquiv s).symm col) := by
  rw [actualBalanceGaussianColumnList_eq_ofFn_symm]
  simp

/-- Every nested-array cell in the serializer agrees with the corresponding
entry of the reindexed finite Gaussian matrix. This closes the position
correspondence between the declared row/column serialization order and the
solver's `Fin` indices. -/
theorem actualBalanceGaussianSerializedCell_eq_rawMatrix {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s)
    (row : Fin (4 * ((3 * s) * (3 * s))))
    (col : Fin ((3 * s) * (3 * s))) :
    ((actualBalanceSerializedCoefficientMatrix
        (decodeRawArray (n := 3 * s) raw) tape)[row.val]?.bind
      fun rowArray => rowArray[col.val]?) =
      some (actualBalanceGaussianRawMatrix raw tape row col) := by
  rw [actualBalanceSerializedCoefficientMatrix_row_spec
    (decodeRawArray (n := 3 * s) raw) tape row.val col.val
    ((actualBalanceGaussianRowEquiv s).symm row)
    ((actualBalanceGaussianColumnEquiv s).symm col)
    (actualBalanceGaussianRowList_getElem?_equiv s row)
    (actualBalanceGaussianColumnList_getElem?_equiv s col)]
  simp [actualBalanceGaussianRawMatrix, Matrix.reindex_apply,
    Matrix.submatrix_apply, actualBalanceRawInputCoefficientMatrix]

end CorruptedFieldRecovery
