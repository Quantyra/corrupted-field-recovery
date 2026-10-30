import CorruptedFieldRecovery.S010BalanceRawInputMatrix
import Mathlib.Data.List.OfFn

namespace CorruptedFieldRecovery

/-- Deterministically select the first row, in `Fin` order, whose entry in the
chosen column is one. This is the pivot search used by the binary eliminator. -/
def balanceFirstPivotRow {m n : Nat}
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) (column : Fin n) : Option (Fin m) :=
  (List.ofFn fun i : Fin m => i).find? fun i => decide (A i column = 1)

theorem balanceFirstPivotRow_sound {m n : Nat}
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) (column : Fin n)
    {row : Fin m} (h : balanceFirstPivotRow A column = some row) :
    A row column = 1 := by
  have hfind := (List.find?_ofFn_eq_some_of_injective
    (f := fun i : Fin m => i)
    (p := fun i => decide (A i column = 1))
    (i := row) Function.injective_id).mp h
  exact of_decide_eq_true hfind.1

end CorruptedFieldRecovery
