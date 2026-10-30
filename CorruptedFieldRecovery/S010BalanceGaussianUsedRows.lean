import CorruptedFieldRecovery.S010BalanceGaussianProcessedColumns

namespace CorruptedFieldRecovery

theorem balanceGaussianColumnScan_used_eq_start_union_pivotRows
    {m n : Nat} (columns : List (Fin n))
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) (used : Finset (Fin m)) :
    balanceGaussianColumnScanUsed A used columns =
      used ∪ ((balanceGaussianColumnScan A used columns).2.map Prod.fst).toFinset := by
  revert A used
  induction columns with
  | nil =>
      intro A used
      simp [balanceGaussianColumnScanUsed, balanceGaussianColumnScan]
  | cons column columns ih =>
      intro A used
      cases h : balanceFirstUnusedPivotRow A column used with
      | none =>
          simpa [balanceGaussianColumnScanUsed, balanceGaussianColumnScan, h]
            using ih A used
      | some row =>
          let rest := balanceGaussianColumnScan
            (balanceGaussianPivotRow A row column) (insert row used) columns
          have htail := ih (balanceGaussianPivotRow A row column) (insert row used)
          apply Finset.ext
          intro i
          simp [balanceGaussianColumnScanUsed, balanceGaussianColumnScan,
            h, htail, Finset.mem_union, Finset.mem_insert]

theorem balanceGaussianColumnScanUsed_empty_eq_pivotRows
    {m n : Nat} (columns : List (Fin n))
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    balanceGaussianColumnScanUsed A ∅ columns =
      ((balanceGaussianColumnScan A ∅ columns).2.map Prod.fst).toFinset := by
  rw [balanceGaussianColumnScan_used_eq_start_union_pivotRows]
  simp

end CorruptedFieldRecovery
