import CorruptedFieldRecovery.S010BalanceGaussianFreeRows

namespace CorruptedFieldRecovery

theorem balanceGaussianColumnScan_pivots_fresh {m n : Nat}
    (columns : List (Fin n)) (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (used : Finset (Fin m)) :
    ∀ pivot ∈ (balanceGaussianColumnScan A used columns).2,
      pivot.1 ∉ used := by
  revert A used
  induction columns with
  | nil =>
      intro A used pivot hpivot
      simp [balanceGaussianColumnScan] at hpivot
  | cons column columns ih =>
      intro A used pivot hpivot
      cases h : balanceFirstUnusedPivotRow A column used with
      | none =>
          have hmem : pivot ∈ (balanceGaussianColumnScan A used columns).2 := by
            simpa [balanceGaussianColumnScan, h] using hpivot
          exact ih A used pivot hmem
      | some row =>
          let rest := balanceGaussianColumnScan
            (balanceGaussianPivotRow A row column) (insert row used) columns
          have hmem : pivot = (row, column) ∨ pivot ∈ rest.2 := by
            simpa [balanceGaussianColumnScan, h, rest] using hpivot
          rcases hmem with hhead | htail
          · subst pivot
            exact (balanceFirstUnusedPivotRow_sound A column used h).1
          · have hfresh := ih
              (balanceGaussianPivotRow A row column) (insert row used) pivot htail
            intro hused
            exact hfresh (Finset.mem_insert.mpr (Or.inr hused))

theorem balanceGaussianColumnScan_pivotRows_nodup {m n : Nat}
    (columns : List (Fin n)) (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (used : Finset (Fin m)) :
    List.Nodup ((balanceGaussianColumnScan A used columns).2.map Prod.fst) := by
  revert A used
  induction columns with
  | nil =>
      intro A used
      simp [balanceGaussianColumnScan]
  | cons column columns ih =>
      intro A used
      cases h : balanceFirstUnusedPivotRow A column used with
      | none =>
          simpa [balanceGaussianColumnScan, h] using ih A used
      | some row =>
          let rest := balanceGaussianColumnScan
            (balanceGaussianPivotRow A row column) (insert row used) columns
          have htail := ih (balanceGaussianPivotRow A row column) (insert row used)
          have hhead : row ∉ rest.2.map Prod.fst := by
            intro hmem
            rcases List.mem_map.mp hmem with ⟨pivot, hpivot, hrow⟩
            have hfresh := balanceGaussianColumnScan_pivots_fresh
              columns (balanceGaussianPivotRow A row column) (insert row used)
              pivot hpivot
            have hrowUsed : pivot.1 ∈ insert row used := by
              exact Finset.mem_insert.mpr (Or.inl hrow)
            exact hfresh hrowUsed
          simp only [balanceGaussianColumnScan, h, List.map_cons]
          exact List.nodup_cons.mpr ⟨hhead, by simpa [rest] using htail⟩

end CorruptedFieldRecovery
