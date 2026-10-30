import CorruptedFieldRecovery.S010BalanceGaussianStructure

namespace CorruptedFieldRecovery

theorem balanceGaussianColumnScan_pivotColumns_mem {m n : Nat}
    (columns : List (Fin n)) (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (used : Finset (Fin m)) :
    ∀ pivot ∈ (balanceGaussianColumnScan A used columns).2,
      pivot.2 ∈ columns := by
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
          exact List.mem_cons_of_mem column (ih A used pivot hmem)
      | some row =>
          let rest := balanceGaussianColumnScan
            (balanceGaussianPivotRow A row column) (insert row used) columns
          have hmem : pivot = (row, column) ∨ pivot ∈ rest.2 := by
            simpa [balanceGaussianColumnScan, h, rest] using hpivot
          rcases hmem with hhead | htail
          · subst pivot
            exact List.mem_cons_self
          · exact List.mem_cons_of_mem column
              (ih (balanceGaussianPivotRow A row column) (insert row used) pivot htail)

theorem balanceGaussianColumnScan_pivotColumns_nodup {m n : Nat}
    (columns : List (Fin n)) (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (used : Finset (Fin m)) (hcolumns : columns.Nodup) :
    List.Nodup ((balanceGaussianColumnScan A used columns).2.map Prod.snd) := by
  revert A used
  induction columns with
  | nil =>
      intro A used
      simp [balanceGaussianColumnScan]
  | cons column columns ih =>
      intro A used
      rcases List.nodup_cons.mp hcolumns with ⟨hhead, htailNodup⟩
      cases h : balanceFirstUnusedPivotRow A column used with
      | none =>
          simpa [balanceGaussianColumnScan, h] using ih htailNodup A used
      | some row =>
          let rest := balanceGaussianColumnScan
            (balanceGaussianPivotRow A row column) (insert row used) columns
          have htail := ih htailNodup
            (balanceGaussianPivotRow A row column) (insert row used)
          have hnew : column ∉ rest.2.map Prod.snd := by
            intro hmem
            rcases List.mem_map.mp hmem with ⟨pivot, hpivot, hcol⟩
            have hcolTail := balanceGaussianColumnScan_pivotColumns_mem
              columns (balanceGaussianPivotRow A row column) (insert row used)
              pivot hpivot
            exact hhead (by simpa [hcol] using hcolTail)
          simp only [balanceGaussianColumnScan, h, List.map_cons]
          exact List.nodup_cons.mpr ⟨hnew, by simpa [rest] using htail⟩

theorem balanceGaussianColumnScan_nonpivotColumn_zero_on_unusedRows
    {m n : Nat} (columns : List (Fin n))
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) (used : Finset (Fin m))
    (target : Fin n) (htarget : target ∈ columns)
    (hfree : target ∉ (balanceGaussianColumnScan A used columns).2.map Prod.snd) :
    ∀ i, i ∉ balanceGaussianColumnScanUsed A used columns →
      (balanceGaussianColumnScan A used columns).1 i target = 0 := by
  revert A used target
  induction columns with
  | nil =>
      intro A used target htarget
      simp at htarget
  | cons column columns ih =>
      intro A used target htarget hfree i hi
      by_cases htargetHead : target = column
      · subst target
        cases h : balanceFirstUnusedPivotRow A column used with
        | none =>
            have hzero : ∀ j, j ∉ used → A j column = 0 := by
              intro j hj
              exact balanceFirstUnusedPivotRow_none_zero A column used h hj
            have htail := balanceGaussianColumnScan_zero_on_unusedRows
              columns A used column hzero i
            have hiTail : i ∉ balanceGaussianColumnScanUsed A used columns := by
              simpa [balanceGaussianColumnScanUsed, h] using hi
            simpa [balanceGaussianColumnScan, balanceGaussianColumnScanUsed, h]
              using htail hiTail
        | some row =>
            have hpivot : column ∈
                (balanceGaussianColumnScan A used (column :: columns)).2.map Prod.snd := by
              simp [balanceGaussianColumnScan, h]
            exact (hfree hpivot).elim
      · have htargetTail : target ∈ columns := by
          rcases List.mem_cons.mp htarget with heq | htail
          · exact (htargetHead heq).elim
          · exact htail
        cases h : balanceFirstUnusedPivotRow A column used with
        | none =>
            have hfreeTail : target ∉
                (balanceGaussianColumnScan A used columns).2.map Prod.snd := by
              intro hm
              exact hfree (by simpa [balanceGaussianColumnScan, h] using hm)
            have hiTail : i ∉ balanceGaussianColumnScanUsed A used columns := by
              simpa [balanceGaussianColumnScanUsed, h] using hi
            have hresult := ih A used target htargetTail hfreeTail i hiTail
            simpa [balanceGaussianColumnScan, h] using hresult
        | some row =>
            let rest := balanceGaussianColumnScan
              (balanceGaussianPivotRow A row column) (insert row used) columns
            have hfreeTail : target ∉ rest.2.map Prod.snd := by
              intro hm
              apply hfree
              simp [balanceGaussianColumnScan, h, rest, hm, htargetHead]
            have hiTail : i ∉ balanceGaussianColumnScanUsed
                (balanceGaussianPivotRow A row column) (insert row used) columns := by
              simpa [balanceGaussianColumnScanUsed, h] using hi
            have hresult := ih (balanceGaussianPivotRow A row column)
              (insert row used) target htargetTail hfreeTail i hiTail
            simpa [balanceGaussianColumnScan, h, rest] using hresult

end CorruptedFieldRecovery
