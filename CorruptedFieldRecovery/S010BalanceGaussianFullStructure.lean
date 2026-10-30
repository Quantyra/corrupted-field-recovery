import CorruptedFieldRecovery.S010BalanceGaussianUsedRows

namespace CorruptedFieldRecovery

/-- After scanning every column from an empty used-row set, every row with no
recorded pivot is identically zero. This is the full-matrix reduced-row fact
used to construct free-variable kernel vectors. -/
theorem balanceGaussianFullColumnScan_unusedRows_zero {m n : Nat}
    [Fintype (Fin n)] (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (i : Fin m)
    (hi : i ∉ (balanceGaussianColumnScan A ∅
      (List.ofFn fun j : Fin n => j)).2.map Prod.fst) :
    ∀ column, (balanceGaussianColumnScan A ∅
      (List.ofFn fun j : Fin n => j)).1 i column = 0 := by
  intro column
  have hcolumn : column ∈ List.ofFn (fun j : Fin n => j) := by
    rw [List.mem_ofFn']
    exact ⟨column, rfl⟩
  by_cases hpivot : column ∈
      (balanceGaussianColumnScan A ∅
        (List.ofFn fun j : Fin n => j)).2.map Prod.snd
  · rcases List.mem_map.mp hpivot with ⟨pivot, hpivot, hcolumnPivot⟩
    have hrowNot : i ≠ pivot.1 := by
      intro heq
      apply hi
      exact List.mem_map.mpr ⟨pivot, hpivot, heq.symm⟩
    have hunit := balanceGaussianColumnScan_recordedPivots_unit
      (List.ofFn fun j : Fin n => j) A ∅ pivot hpivot
    rw [← hcolumnPivot, hunit i]
    simp [hrowNot]
  · have hiUnused : i ∉ balanceGaussianColumnScanUsed A ∅
        (List.ofFn fun j : Fin n => j) := by
      rw [balanceGaussianColumnScanUsed_empty_eq_pivotRows]
      simpa only [List.mem_toFinset] using hi
    exact balanceGaussianColumnScan_nonpivotColumn_zero_on_unusedRows
      (List.ofFn fun j : Fin n => j) A ∅ column hcolumn hpivot i hiUnused

end CorruptedFieldRecovery
