import CorruptedFieldRecovery.S010BalanceGaussianPivotComplete

namespace CorruptedFieldRecovery

/-- Mask rows already used as pivots so the ordinary deterministic search
selects only a fresh row. -/
def balanceMaskUsedRows {m n : Nat} (used : Finset (Fin m))
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) : Matrix (Fin m) (Fin n) (ZMod 2) :=
  fun i j => if i ∈ used then 0 else A i j

def balanceFirstUnusedPivotRow {m n : Nat}
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) (column : Fin n)
    (used : Finset (Fin m)) : Option (Fin m) :=
  balanceFirstPivotRow (balanceMaskUsedRows used A) column

theorem balanceFirstUnusedPivotRow_sound {m n : Nat}
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) (column : Fin n)
    (used : Finset (Fin m)) {row : Fin m}
    (h : balanceFirstUnusedPivotRow A column used = some row) :
    row ∉ used ∧ A row column = 1 := by
  have hp := balanceFirstPivotRow_sound
    (balanceMaskUsedRows used A) column h
  constructor
  · by_contra hu
    simp [balanceMaskUsedRows, hu] at hp
  · by_cases hu : row ∈ used
    · have hfresh : row ∉ used := by
        by_contra hbad
        simp [balanceMaskUsedRows, hbad] at hp
      exact (hfresh hu).elim
    · simpa [balanceMaskUsedRows, hu] using hp

theorem balanceFirstUnusedPivotRow_complete {m n : Nat}
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) (column : Fin n)
    (used : Finset (Fin m))
    (h : ∃ row, row ∉ used ∧ A row column = 1) :
    ∃ row, balanceFirstUnusedPivotRow A column used = some row := by
  rcases h with ⟨row, hfresh, hone⟩
  have hmasked : ∃ row, balanceMaskUsedRows used A row column = 1 := by
    exact ⟨row, by simpa [balanceMaskUsedRows, hfresh] using hone⟩
  rcases balanceFirstPivotRow_complete (balanceMaskUsedRows used A)
    column hmasked with ⟨row, hpivot⟩
  exact ⟨row, hpivot⟩

end CorruptedFieldRecovery
