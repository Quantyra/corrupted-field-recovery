import CorruptedFieldRecovery.S010BalanceGaussianElimination

namespace CorruptedFieldRecovery

private theorem balanceGaussianPivotRow_preserves_column {m n : Nat}
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) (pivotRow : Fin m)
    (pivotColumn targetColumn : Fin n)
    (hzero : A pivotRow targetColumn = 0) (i : Fin m) :
    balanceGaussianPivotRow A pivotRow pivotColumn i targetColumn =
      A i targetColumn := by
  by_cases hi : i = pivotRow
  · subst i
    simp [balanceGaussianPivotRow]
  · simp [balanceGaussianPivotRow, hi, hzero, mul_zero, add_zero]

/-- Later pivots preserve an earlier unit column: their fresh pivot row is
outside the used set, hence zero in the earlier pivot column. -/
theorem balanceGaussianColumnScan_preserves_pivotColumn {m n : Nat}
    [Fintype (Fin n)] (columns : List (Fin n))
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) (used : Finset (Fin m))
    (pivotRow : Fin m) (pivotColumn : Fin n)
    (hused : pivotRow ∈ used)
    (hunit : ∀ i, A i pivotColumn = if i = pivotRow then 1 else 0) :
    ∀ i, (balanceGaussianColumnScan A used columns).1 i pivotColumn =
      if i = pivotRow then 1 else 0 := by
  revert A used hused hunit
  induction columns with
  | nil =>
      intro A used hused hunit
      exact hunit
  | cons column columns ih =>
      intro A used hused hunit
      cases h : balanceFirstUnusedPivotRow A column used with
      | none =>
          simpa [balanceGaussianColumnScan, h] using
            ih A used hused hunit
      | some row =>
          have hfresh := balanceFirstUnusedPivotRow_sound A column used h
          have hrow_ne : row ≠ pivotRow := by
            intro heq
            have hmem : row ∈ used := by simpa [heq] using hused
            exact hfresh.1 hmem
          have hzero : A row pivotColumn = 0 := by
            have hx := hunit row
            simpa [hrow_ne] using hx
          have hpres := balanceGaussianPivotRow_preserves_column
            A row column pivotColumn hzero
          have hunit' : ∀ i,
              balanceGaussianPivotRow A row column i pivotColumn =
                if i = pivotRow then 1 else 0 := by
            intro i
            rw [hpres i]
            exact hunit i
          have hused' : pivotRow ∈ insert row used := by
            rw [Finset.mem_insert]
            exact Or.inr hused
          simpa [balanceGaussianColumnScan, h] using
            ih (balanceGaussianPivotRow A row column) (insert row used)
              hused' hunit'

end CorruptedFieldRecovery
