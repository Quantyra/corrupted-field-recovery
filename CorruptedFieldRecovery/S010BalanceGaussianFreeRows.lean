import CorruptedFieldRecovery.S010BalanceGaussianPivotInvariant
import Mathlib.Tactic

namespace CorruptedFieldRecovery

private theorem zmodTwo_eq_zero_or_one (z : ZMod 2) : z = 0 ∨ z = 1 := by
  have hv := ZMod.val_lt z
  have h01 : z.val = 0 ∨ z.val = 1 := by omega
  rcases h01 with hz | hone
  · exact Or.inl ((ZMod.val_eq_zero z).mp hz)
  · apply Or.inr
    apply ZMod.val_injective 2
    simpa using hone

theorem balanceFirstUnusedPivotRow_none_zero {m n : Nat}
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) (column : Fin n)
    (used : Finset (Fin m))
    (h : balanceFirstUnusedPivotRow A column used = none)
    {row : Fin m} (hrow : row ∉ used) : A row column = 0 := by
  rcases zmodTwo_eq_zero_or_one (A row column) with hzero | hone
  · exact hzero
  · have hsome := balanceFirstUnusedPivotRow_complete A column used
      ⟨row, hrow, hone⟩
    rw [h] at hsome
    rcases hsome with ⟨pivot, hpivot⟩
    simp at hpivot

private theorem balanceGaussianPivotRow_preserves_zero_column {m n : Nat}
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) (pivotRow : Fin m)
    (pivotColumn targetColumn : Fin n)
    (hzero : A pivotRow targetColumn = 0) (i : Fin m) :
    balanceGaussianPivotRow A pivotRow pivotColumn i targetColumn =
      A i targetColumn := by
  by_cases hi : i = pivotRow
  · subst i
    simp [balanceGaussianPivotRow]
  · simp [balanceGaussianPivotRow, hi, hzero, mul_zero, add_zero]

/-- Keep track of the used-row state corresponding to the operation list
returned by the deterministic column scan. -/
def balanceGaussianColumnScanUsed {m n : Nat}
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    Finset (Fin m) → List (Fin n) → Finset (Fin m)
  | used, [] => used
  | used, column :: columns =>
      match balanceFirstUnusedPivotRow A column used with
      | none => balanceGaussianColumnScanUsed A used columns
      | some row =>
          balanceGaussianColumnScanUsed
            (balanceGaussianPivotRow A row column) (insert row used) columns

theorem balanceGaussianColumnScan_zero_on_unusedRows {m n : Nat}
    (columns : List (Fin n)) (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (used : Finset (Fin m)) (targetColumn : Fin n)
    (hzero : ∀ i, i ∉ used → A i targetColumn = 0) :
    ∀ i, i ∉ balanceGaussianColumnScanUsed A used columns →
      (balanceGaussianColumnScan A used columns).1 i targetColumn = 0 := by
  revert A used hzero
  induction columns with
  | nil =>
      intro A used hzero i hi
      exact hzero i hi
  | cons column columns ih =>
      intro A used hzero i hi
      cases h : balanceFirstUnusedPivotRow A column used with
      | none =>
          have hi' : i ∉ balanceGaussianColumnScanUsed A used columns := by
            simpa [balanceGaussianColumnScanUsed, h] using hi
          have htail := ih A used hzero i hi'
          simpa [balanceGaussianColumnScan, h] using htail
      | some row =>
          have hfresh := balanceFirstUnusedPivotRow_sound A column used h
          have hrowZero := hzero row hfresh.1
          have hzero' : ∀ j, j ∉ insert row used →
              balanceGaussianPivotRow A row column j targetColumn = 0 := by
            intro j hj
            have hjused : j ∉ used := by
              intro hmem
              exact hj (Finset.mem_insert.mpr (Or.inr hmem))
            rw [balanceGaussianPivotRow_preserves_zero_column
              A row column targetColumn hrowZero j]
            exact hzero j hjused
          have hi' : i ∉ balanceGaussianColumnScanUsed
              (balanceGaussianPivotRow A row column) (insert row used) columns := by
            simpa [balanceGaussianColumnScanUsed, h] using hi
          have htail := ih (balanceGaussianPivotRow A row column)
            (insert row used) hzero' i hi'
          simpa [balanceGaussianColumnScan, h] using htail

end CorruptedFieldRecovery
