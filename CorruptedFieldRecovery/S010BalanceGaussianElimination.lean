import CorruptedFieldRecovery.S010BalanceGaussianCore
import CorruptedFieldRecovery.S010BalanceGaussianUnusedPivot

open scoped Matrix

namespace CorruptedFieldRecovery

/-- Process one column: if a fresh pivot exists, use it to clear every other
entry in that column. -/
def balanceGaussianColumnStep {m n : Nat}
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) (column : Fin n)
    (used : Finset (Fin m)) : Matrix (Fin m) (Fin n) (ZMod 2) :=
  match balanceFirstUnusedPivotRow A column used with
  | none => A
  | some row => balanceGaussianPivotRow A row column

theorem balanceGaussianColumnStep_pivot_column {m n : Nat}
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) (column : Fin n)
    (used : Finset (Fin m)) {row : Fin m}
    (h : balanceFirstUnusedPivotRow A column used = some row) (i : Fin m) :
    balanceGaussianColumnStep A column used i column = if i = row then 1 else 0 := by
  have hp := balanceFirstUnusedPivotRow_sound A column used h
  by_cases hi : i = row
  · subst i
    simp [balanceGaussianColumnStep, h, balanceGaussianPivotRow, hp.2]
  · simp [balanceGaussianColumnStep, h, balanceGaussianPivotRow, hi, hp.2,
      ZModModule.add_self]

theorem balanceGaussianColumnStep_kernel_iff {m n : Nat}
    [Fintype (Fin n)] (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (column : Fin n) (used : Finset (Fin m)) (x : Fin n → ZMod 2) :
    balanceGaussianColumnStep A column used *ᵥ x = 0 ↔ A *ᵥ x = 0 := by
  cases h : balanceFirstUnusedPivotRow A column used with
  | none => simp [balanceGaussianColumnStep, h]
  | some row =>
      simpa [balanceGaussianColumnStep, h] using
        (balanceGaussianPivotRow_mulVec_zero_iff A row column x)

/-- Scan columns in their supplied order. The selected pivot row is marked as
used, and the returned operation list records exactly the executed updates. -/
def balanceGaussianColumnScan {m n : Nat}
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    Finset (Fin m) → List (Fin n) →
      Matrix (Fin m) (Fin n) (ZMod 2) × List (Fin m × Fin n)
  | _, [] => (A, [])
  | used, column :: columns =>
      match balanceFirstUnusedPivotRow A column used with
      | none => balanceGaussianColumnScan A used columns
      | some row =>
          let rest := balanceGaussianColumnScan
            (balanceGaussianPivotRow A row column) (insert row used) columns
          (rest.1, (row, column) :: rest.2)

theorem balanceGaussianColumnScan_kernel_iff {m n : Nat}
    [Fintype (Fin n)] (columns : List (Fin n))
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) (used : Finset (Fin m))
    (x : Fin n → ZMod 2) :
    (balanceGaussianColumnScan A used columns).1 *ᵥ x = 0 ↔
      A *ᵥ x = 0 := by
  induction columns generalizing A used with
  | nil => rfl
  | cons column columns ih =>
      cases h : balanceFirstUnusedPivotRow A column used with
      | none =>
          simpa [balanceGaussianColumnScan, h] using ih A used
      | some row =>
          simpa [balanceGaussianColumnScan, h] using
            (ih (balanceGaussianPivotRow A row column) (insert row used)).trans
              (balanceGaussianPivotRow_mulVec_zero_iff A row column x)

end CorruptedFieldRecovery
