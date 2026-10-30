import CorruptedFieldRecovery.S010BalanceGaussianPivotSearch

namespace CorruptedFieldRecovery

private def listFirstMatch {α : Type} : List α → (α → Bool) → Option α
  | [], _ => none
  | a :: as, p => if p a then some a else listFirstMatch as p

private theorem listFirstMatch_eq_find? {α : Type} (xs : List α)
    (p : α → Bool) : listFirstMatch xs p = xs.find? p := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
      cases h : p a <;> simp [listFirstMatch, List.find?, h, ih]

private theorem listFirstMatch_some_of_mem {α : Type} (xs : List α)
    (p : α → Bool) {a : α} (ha : a ∈ xs) (hp : p a = true) :
    ∃ b, listFirstMatch xs p = some b := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
      by_cases hx : p x = true
      · exact ⟨x, by simp [listFirstMatch, hx]⟩
      · have htail : a ∈ xs := by
          have ha' : a = x ∨ a ∈ xs := by simpa using ha
          rcases ha' with hax | htailMem
          · have hp' : p x = true := by simpa [hax] using hp
            exact False.elim (hx hp')
          · exact htailMem
        obtain ⟨b, hb⟩ := ih htail
        exact ⟨b, by simp [listFirstMatch, hx, hb]⟩

theorem balanceFirstPivotRow_complete {m n : Nat}
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) (column : Fin n)
    (h : ∃ row, A row column = 1) :
    ∃ row, balanceFirstPivotRow A column = some row := by
  rcases h with ⟨row, hrow⟩
  have hmem : row ∈ List.ofFn (fun i : Fin m => i) := by
    rw [List.mem_ofFn']
    exact ⟨row, rfl⟩
  have hp : decide (A row column = 1) = true := decide_eq_true hrow
  obtain ⟨picked, hpicked⟩ := listFirstMatch_some_of_mem
    (List.ofFn fun i : Fin m => i)
    (fun i => decide (A i column = 1)) hmem hp
  have heq := listFirstMatch_eq_find?
    (List.ofFn fun i : Fin m => i)
    (fun i => decide (A i column = 1))
  refine ⟨picked, ?_⟩
  change (List.ofFn fun i : Fin m => i).find?
    (fun i => decide (A i column = 1)) = some picked
  rw [← heq]
  exact hpicked

end CorruptedFieldRecovery
