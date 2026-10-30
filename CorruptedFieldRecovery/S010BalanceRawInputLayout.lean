import CorruptedFieldRecovery.S010BalanceRawInputMatrix
import Mathlib.Tactic

namespace CorruptedFieldRecovery

theorem actualBalanceCoordinateList_length (n : Nat) :
    (actualBalanceCoordinateList n).length = n := by
  simp [actualBalanceCoordinateList]

private theorem sum_map_const {α : Type} (l : List α) (k : Nat) :
    (l.map fun _ => k).sum = l.length * k := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        Nat.succ_mul, ih]
      omega

private theorem coordinateArea_length (s : Nat) :
    ((actualBalanceCoordinateList (3 * s)).map fun _ => 3 * s).sum =
      (3 * s) * (3 * s) := by
  calc
    _ = (actualBalanceCoordinateList (3 * s)).length * (3 * s) :=
      sum_map_const _ _
    _ = (3 * s) * (3 * s) := by rw [actualBalanceCoordinateList_length]

theorem actualBalanceColumnList_length (s : Nat) :
    (actualBalanceColumnList s).length = (3 * s) * (3 * s) := by
  simp only [actualBalanceColumnList, List.length_flatMap, List.length_map,
    actualBalanceCoordinateList_length]
  exact coordinateArea_length s

theorem actualBalanceRowList_length (s : Nat) :
    (actualBalanceRowList s).length = 4 * (3 * s) * (3 * s) := by
  simp only [actualBalanceRowList, List.length_flatMap, List.length_map,
    actualBalanceCoordinateList_length]
  calc
    _ = (List.ofFn (fun i : Fin 4 => i)).length *
        ((actualBalanceCoordinateList (3 * s)).map fun _ => 3 * s).sum := by
      exact sum_map_const _ _
    _ = 4 * ((actualBalanceCoordinateList (3 * s)).map fun _ => 3 * s).sum := by
      simp
    _ = 4 * ((3 * s) * (3 * s)) := by rw [coordinateArea_length]
    _ = 4 * (3 * s) * (3 * s) := by ring

theorem actualBalanceSerializedRow_width {s : Nat}
    (A : BinaryTensor (3 * s)) (tape : FiveWordTape s)
    (row : ActualBalanceBasisRow s) :
    (((actualBalanceColumnList s).map fun col =>
      actualBalanceComputableCoefficientMatrix A tape row col).toArray).size =
        (3 * s) * (3 * s) := by
  simp [actualBalanceColumnList_length]

theorem actualBalanceSerializedCoefficientMatrix_exact_outer_size {s : Nat}
    (A : BinaryTensor (3 * s)) (tape : FiveWordTape s) :
    (actualBalanceSerializedCoefficientMatrix A tape).size =
      4 * (3 * s) * (3 * s) := by
  rw [actualBalanceSerializedCoefficientMatrix_outer_size,
    actualBalanceRowList_length]

end CorruptedFieldRecovery
