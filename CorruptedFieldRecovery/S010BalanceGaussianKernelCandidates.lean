import CorruptedFieldRecovery.S010BalanceGaussianFullStructure

namespace CorruptedFieldRecovery

/-- Build the candidate kernel vector for a free column by adding the pivot
columns weighted by their entries in that free column. The finite sum and
coordinate vectors are executable over `ZMod 2`. -/
def balanceGaussianFreeKernelCandidate {m n : Nat}
    (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (pivots : List (Fin m × Fin n)) (free : Fin n) : Fin n → ZMod 2 :=
  Pi.single free (1 : ZMod 2) +
    ∑ pivot ∈ pivots.toFinset,
      (A pivot.1 free) • Pi.single pivot.2 1

/-- On every nonpivot column, the free-variable candidates have the identity
coordinate matrix. In particular, the candidate associated to `free` retains
coefficient one there and every other free candidate has coefficient zero. -/
theorem balanceGaussianFreeKernelCandidate_apply_freeColumn
    {m n : Nat} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (pivots : List (Fin m × Fin n)) (free column : Fin n)
    (hcolumn : column ∉ pivots.map Prod.snd) :
    balanceGaussianFreeKernelCandidate A pivots free column =
      if column = free then 1 else 0 := by
  have hterm : ∀ pivot ∈ pivots.toFinset,
      ((A pivot.1 free) •
        (Pi.single pivot.2 (1 : ZMod 2) : Fin n → ZMod 2)) column = 0 := by
    intro pivot hpivot
    have hcolumn' : pivot.2 ≠ column := by
      intro heq
      apply hcolumn
      exact List.mem_map.mpr
        ⟨pivot, List.mem_toFinset.mp hpivot, heq⟩
    simp [hcolumn']
  simp only [balanceGaussianFreeKernelCandidate, Pi.add_apply,
    Finset.sum_apply, Pi.smul_apply]
  rw [Finset.sum_eq_zero]
  · by_cases h : column = free
    · subst column
      simp
    · simp [h]
  · intro pivot hpivot
    simpa only [Pi.smul_apply] using hterm pivot hpivot

end CorruptedFieldRecovery
