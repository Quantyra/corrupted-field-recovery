import CorruptedFieldRecovery.S010BalanceGaussianKernelCandidates
import Mathlib.LinearAlgebra.Matrix.ToLin

open scoped Matrix

namespace CorruptedFieldRecovery

/-- The explicit free-variable correction vector lies in the kernel whenever
the recorded pivot columns are unit columns and all nonpivot rows vanish in
the chosen free column. These hypotheses are supplied by the full scan
structure theorems, rather than by a reduced-form assumption. -/
theorem balanceGaussianFreeKernelCandidate_mem_ker
    {m n : Nat} [Fintype (Fin n)]
    (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (pivots : List (Fin m × Fin n)) (free : Fin n)
    (_hfree : free ∉ pivots.map Prod.snd)
    (hrows : (pivots.map Prod.fst).Nodup)
    (hunit : ∀ pivot ∈ pivots, ∀ i,
      A i pivot.2 = if i = pivot.1 then 1 else 0)
    (hzero : ∀ i, i ∉ pivots.map Prod.fst → A i free = 0) :
    A *ᵥ balanceGaussianFreeKernelCandidate A pivots free = 0 := by
  classical
  let P := pivots.toFinset
  let L := Matrix.mulVecBilin (ZMod 2) (ZMod 2) A
  have hcalc :
      A *ᵥ balanceGaussianFreeKernelCandidate A pivots free =
        A.col free +
          ∑ pivot ∈ P, (A pivot.1 free) • A.col pivot.2 := by
    change L (Pi.single free 1 +
      ∑ pivot ∈ P, (A pivot.1 free) • Pi.single pivot.2 1) = _
    rw [map_add, map_sum]
    simp [L, Matrix.mulVecBilin_apply]
  have hsumRewrite (i : Fin m) :
      (∑ pivot ∈ P, (A pivot.1 free) • A i pivot.2) =
        ∑ pivot ∈ P,
          if i = pivot.1 then A pivot.1 free else 0 := by
    apply Finset.sum_congr rfl
    intro pivot hpivot
    have hpivot' : pivot ∈ pivots := List.mem_toFinset.mp hpivot
    rw [hunit pivot hpivot' i]
    by_cases hrow : i = pivot.1 <;> simp [hrow]
  apply funext
  intro i
  have hrowCalc := congrFun hcalc i
  simp only [Matrix.col_apply, Pi.add_apply, Finset.sum_apply,
    Pi.smul_apply] at hrowCalc
  rw [hrowCalc, hsumRewrite]
  by_cases hi : i ∈ pivots.map Prod.fst
  · rcases List.mem_map.mp hi with ⟨pivot, hpivot, hpi⟩
    have hpivotSet : pivot ∈ P := List.mem_toFinset.mpr hpivot
    have hsum :
        (∑ q ∈ P, if i = q.1 then A q.1 free else 0) = A i free := by
      calc
        _ = (if i = pivot.1 then A pivot.1 free else 0) := by
          rw [Finset.sum_eq_single pivot]
          · intro q hq hqp
            by_cases hqi : i = q.1
            · have hqList : q ∈ pivots := List.mem_toFinset.mp hq
              have hrowEq : q.1 = pivot.1 := hqi.symm.trans hpi.symm
              have hqp' := List.inj_on_of_nodup_map hrows
                hqList hpivot hrowEq
              exact (hqp hqp').elim
            · simp [hqi]
          · simp [hpivotSet]
        _ = A i free := by simp [hpi]
    rw [hsum]
    rw [← hpi]
    exact ZModModule.add_self _
  · have hsum : (∑ q ∈ P, if i = q.1 then A q.1 free else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro q hq
      have hqList : q ∈ pivots := List.mem_toFinset.mp hq
      have hne : i ≠ q.1 := by
        intro heq
        apply hi
        exact List.mem_map.mpr ⟨q, hqList, heq.symm⟩
      simp [hne]
    rw [hsum, hzero i hi]
    simp

end CorruptedFieldRecovery
