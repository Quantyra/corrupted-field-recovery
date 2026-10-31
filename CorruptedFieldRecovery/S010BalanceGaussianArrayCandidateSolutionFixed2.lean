import CorruptedFieldRecovery.S010BalanceGaussianArrayGreedySpan

open scoped Matrix

namespace CorruptedFieldRecovery

/-! # Exact affine equation for the selected array-kernel candidate

Disjoint uncompiled proof bridge. The array span witness records a free
column whose canonical free-kernel vector has final coordinate one. This file
shows that the *same returned candidate*, restricted to the original column
coordinates, solves the requested affine system. It does not use an
existentially chosen coefficient vector.
-/

private theorem actualArrayCandidate_find_test_of_some {α : Type*}
    (test : α → Bool) (xs : List α) {a : α}
    (h : xs.find? test = some a) : test a = true := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
      by_cases hx : test x = true
      · simp [hx] at h
        subst a
        exact hx
      · simp [hx] at h
        exact ih h

/-- If the actual array selector returns a free index, its exact canonical
free-kernel candidate, restricted to the original coefficient coordinates,
solves the target equation. -/
theorem actualGreedyArraySpanWitness?_selectedCandidate_solves
    {m : Nat} (columns : Array (Fin m → ZMod 2))
    (target : Fin m → ZMod 2) {free : Fin (columns.size + 1)}
    (hfound : actualGreedyArraySpanWitness? columns target = some free) :
    let run := actualGreedyArrayAugmentedScan columns target
    let candidate := balanceGaussianFreeKernelCandidate
      (actualBalanceGaussianArrayView
        (m := m) (n := columns.size + 1) run.1) run.2 free
    actualGreedyArraySpanMatrix columns *ᵥ
      (fun i => candidate i.castSucc) = target := by
  classical
  let run := actualGreedyArrayAugmentedScan columns target
  let A := actualGreedyArrayAugmentedMatrix columns target
  let allColumns := List.ofFn (fun col : Fin (columns.size + 1) => col)
  let scan := balanceGaussianColumnScan A ∅ allColumns
  let pivots := scan.2
  let candidate := balanceGaussianFreeKernelCandidate
    (actualBalanceGaussianArrayView
      (m := m) (n := columns.size + 1) run.1) run.2 free
  have htest : actualGreedyArraySpanCandidateTest run free = true := by
    unfold actualGreedyArraySpanWitness? at hfound
    exact actualArrayCandidate_find_test_of_some
      (actualGreedyArraySpanCandidateTest run)
      (List.ofFn fun col : Fin (columns.size + 1) => col) hfound
  have hparts :
      decide (free ∉ run.2.map Prod.snd) = true ∧
      decide (balanceGaussianFreeKernelCandidate
        (actualBalanceGaussianArrayView
          (m := m) (n := columns.size + 1) run.1)
        run.2 free (Fin.last columns.size) = 1) = true := by
    simpa only [actualGreedyArraySpanCandidateTest, Bool.and_eq_true] using htest
  have hfree : free ∉ run.2.map Prod.snd := of_decide_eq_true hparts.1
  have hlast : candidate (Fin.last columns.size) = 1 := of_decide_eq_true hparts.2
  have hscanPair := actualGreedyArrayAugmentedScan_refines columns target
  have hmatrix :
      actualBalanceGaussianArrayView
          (m := m) (n := columns.size + 1)
          (actualGreedyArrayAugmentedScan columns target).1 = scan.1 := by
    change actualBalanceGaussianArrayView
        (m := m) (n := columns.size + 1)
        (actualGreedyArrayAugmentedScan columns target).1 =
      (balanceGaussianColumnScan
        (actualGreedyArrayAugmentedMatrix columns target) ∅
        (List.ofFn fun col : Fin (columns.size + 1) => col)).1
    exact congrArg Prod.fst hscanPair
  have hpivots : run.2 = pivots := by
    change (actualGreedyArrayAugmentedScan columns target).2 =
      (balanceGaussianColumnScan A ∅ allColumns).2
    exact congrArg Prod.snd hscanPair
  have hrows : (pivots.map Prod.fst).Nodup := by
    simpa [pivots, scan] using
      balanceGaussianColumnScan_pivotRows_nodup allColumns A ∅
  have hunit : ∀ pivot ∈ pivots, ∀ i,
      scan.1 i pivot.2 = if i = pivot.1 then 1 else 0 := by
    intro pivot hpivot i
    exact balanceGaussianColumnScan_recordedPivots_unit
      allColumns A ∅ pivot hpivot i
  have hzero : ∀ i, i ∉ pivots.map Prod.fst → scan.1 i = 0 := by
    intro i hi
    funext col
    exact balanceGaussianFullColumnScan_unusedRows_zero A i hi col
  have hcandidateKernel : scan.1 *ᵥ
      (balanceGaussianFreeKernelCandidate scan.1 pivots free) = 0 := by
    have hfree' : free ∉ pivots.map Prod.snd := by
      rw [← hpivots]
      exact hfree
    apply balanceGaussianFreeKernelCandidate_mem_ker
      _ pivots free hfree' hrows hunit
    intro i hi
    exact congrFun (hzero i hi) free
  have hkernelArray :
      actualBalanceGaussianArrayView (m := m) (n := columns.size + 1) run.1 *ᵥ
        candidate = 0 := by
    change actualBalanceGaussianArrayView
        (m := m) (n := columns.size + 1)
        (actualGreedyArrayAugmentedScan columns target).1 *ᵥ
        balanceGaussianFreeKernelCandidate
          (actualBalanceGaussianArrayView
            (m := m) (n := columns.size + 1)
            (actualGreedyArrayAugmentedScan columns target).1)
          (actualGreedyArrayAugmentedScan columns target).2 free = 0
    rw [hmatrix, hpivots]
    exact hcandidateKernel
  have hkernelInput :=
    (actualBalanceGaussianArrayFullColumnScan_kernel_iff
      (actualGreedyArrayAugmentedCells columns target) candidate).mp hkernelArray
  have hinputMatrix :
      actualBalanceGaussianArrayView (m := m) (n := columns.size + 1)
        (actualGreedyArrayAugmentedCells columns target) = A :=
    actualGreedyArrayAugmentedCells_view columns target
  have haug : A *ᵥ candidate = 0 := by
    rw [← hinputMatrix]
    exact hkernelInput
  let coeff : Fin columns.size → ZMod 2 := fun i => candidate i.castSucc
  have hdecomp : candidate = Fin.snoc coeff 1 := by
    funext i
    refine Fin.lastCases ?_ ?_ i
    · simpa [coeff] using hlast
    · intro j
      simp [coeff]
  have hsum : actualGreedyArraySpanMatrix columns *ᵥ coeff + target = 0 := by
    rw [hdecomp, actualGreedyArrayAugmentedMatrix_mulVec_snoc] at haug
    exact haug
  have hsolve : actualGreedyArraySpanMatrix columns *ᵥ coeff = target := by
    apply funext
    intro row
    have hrow := congrFun hsum row
    simp only [Pi.add_apply, Pi.zero_apply] at hrow
    calc
      (actualGreedyArraySpanMatrix columns *ᵥ coeff) row =
          (actualGreedyArraySpanMatrix columns *ᵥ coeff) row + 0 := by simp
      _ = (actualGreedyArraySpanMatrix columns *ᵥ coeff) row +
          (target row + target row) := by rw [ZModModule.add_self]
      _ = ((actualGreedyArraySpanMatrix columns *ᵥ coeff) row + target row) +
          target row := by rw [← add_assoc]
      _ = 0 + target row := by rw [hrow]
      _ = target row := by simp
  simpa [coeff, candidate, run] using hsolve

end CorruptedFieldRecovery
