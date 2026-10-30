import CorruptedFieldRecovery.S010BalanceGaussianKernelSpan

open scoped Matrix

namespace CorruptedFieldRecovery

/-- Pivot-row equations force a kernel vector to vanish when all its free
coordinates vanish. The hypotheses are exactly the recorded-pivot facts: each
pivot column is its unit vector, and distinct recorded pivots have distinct
rows. -/
theorem balanceGaussianKernel_zero_of_freeCoordinates_zero
    {m n : Nat} [Fintype (Fin n)]
    (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (pivots : List (Fin m × Fin n)) (x : Fin n → ZMod 2)
    (hrows : (pivots.map Prod.fst).Nodup)
    (hunit : ∀ pivot ∈ pivots, ∀ i,
      A i pivot.2 = if i = pivot.1 then 1 else 0)
    (hfreezero : ∀ column, column ∉ pivots.map Prod.snd → x column = 0)
    (hker : A *ᵥ x = 0) :
    x = 0 := by
  classical
  apply funext
  intro column
  by_cases hfree : column ∉ pivots.map Prod.snd
  · exact hfreezero column hfree
  · have hpivotCol : column ∈ pivots.map Prod.snd := by
      by_contra hnot
      exact hfree hnot
    rcases List.mem_map.mp hpivotCol with ⟨pivot, hpivot, hpivotColumn⟩
    have hrow := congrFun hker pivot.1
    have hsum : (∑ j : Fin n, A pivot.1 j * x j) = 0 := by
      simpa [Matrix.mulVec, dotProduct] using hrow
    have hsum_eq : (∑ j : Fin n, A pivot.1 j * x j) = x pivot.2 := by
      calc
        _ = A pivot.1 pivot.2 * x pivot.2 := by
          rw [Finset.sum_eq_single pivot.2]
          · intro j hj hji
            by_cases hjfree : j ∉ pivots.map Prod.snd
            · simp [hfreezero j hjfree]
            · have hjpivot : j ∈ pivots.map Prod.snd := by
                by_contra hnot
                exact hjfree hnot
              rcases List.mem_map.mp hjpivot with ⟨q, hq, hqColumn⟩
              have hpivotNe : pivot ≠ q := by
                intro heq
                apply hji
                calc
                  j = q.2 := hqColumn.symm
                  _ = pivot.2 := by rw [heq]
              have hrowNe : pivot.1 ≠ q.1 := by
                intro heq
                have heqpivot := List.inj_on_of_nodup_map hrows
                  hpivot hq heq
                exact hpivotNe heqpivot
              have hqEntry := hunit q hq pivot.1
              rw [← hqColumn, hqEntry]
              simp [hrowNe]
          · simp
        _ = x pivot.2 := by
          have hpivotEntry : A pivot.1 pivot.2 = 1 := by
            rw [hunit pivot hpivot pivot.1]
            simp
          simp [hpivotEntry]
    have hxPivot : x pivot.2 = 0 := by
      rw [← hsum_eq]
      exact hsum
    simpa [hpivotColumn] using hxPivot

/-- The explicit free-coordinate reconstruction theorem specialized to a
kernel whose zero-free-coordinate case is settled by the pivot equations. -/
theorem balanceGaussianFreeCandidateFamily_reconstruct_of_pivotRows
    {m n : Nat} [Fintype (Fin n)]
    (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (pivots : List (Fin m × Fin n))
    [Fintype (balanceGaussianFreeIndex pivots)]
    (hrows : (pivots.map Prod.fst).Nodup)
    (hunit : ∀ pivot ∈ pivots, ∀ i,
      A i pivot.2 = if i = pivot.1 then 1 else 0)
    (hcandidate : ∀ free : balanceGaussianFreeIndex pivots,
      A *ᵥ balanceGaussianFreeCandidateFamily A pivots free = 0) :
    ∀ x : Fin n → ZMod 2, A *ᵥ x = 0 →
      x = ∑ free : balanceGaussianFreeIndex pivots,
        x free.1 • balanceGaussianFreeCandidateFamily A pivots free := by
  classical
  have hunique : ∀ y : Fin n → ZMod 2, A *ᵥ y = 0 →
      (∀ free : balanceGaussianFreeIndex pivots, y free.1 = 0) → y = 0 := by
    intro y hy hfree
    apply balanceGaussianKernel_zero_of_freeCoordinates_zero A pivots y
      hrows hunit ?_ hy
    intro column hcolumn
    exact hfree ⟨column, hcolumn⟩
  intro x hx
  exact balanceGaussianFreeCandidateFamily_reconstruct A pivots
    hcandidate hunique x hx

/-- The concrete candidates returned from the complete deterministic column
scan are linearly independent, by their identity coordinates on the columns
that the scan did not pivot. -/
theorem balanceGaussianFullColumnScan_candidates_linearIndependent
    {m n : Nat} [Fintype (Fin n)]
    (A : Matrix (Fin m) (Fin n) (ZMod 2))
    [Fintype (balanceGaussianFreeIndex
      (balanceGaussianColumnScan A ∅ (List.ofFn fun j : Fin n => j)).2)] :
    LinearIndependent (ZMod 2)
      (balanceGaussianFreeCandidateFamily
        (balanceGaussianColumnScan A ∅ (List.ofFn fun j : Fin n => j)).1
        (balanceGaussianColumnScan A ∅ (List.ofFn fun j : Fin n => j)).2) := by
  classical
  exact balanceGaussianFreeCandidateFamily_linearIndependent _ _

/-- Every vector in the kernel of the actual full scan matrix is the explicit
free-coordinate combination of the executable candidates. The proof derives
candidate kernel membership from the full scan's unit pivot columns and zero
unused rows, then invokes the pivot-row uniqueness argument above. -/
theorem balanceGaussianFullColumnScan_candidates_reconstruct
    {m n : Nat} [Fintype (Fin n)]
    (A : Matrix (Fin m) (Fin n) (ZMod 2))
    [Fintype (balanceGaussianFreeIndex
      (balanceGaussianColumnScan A ∅ (List.ofFn fun j : Fin n => j)).2)] :
    ∀ x : Fin n → ZMod 2,
      (balanceGaussianColumnScan A ∅
        (List.ofFn fun j : Fin n => j)).1 *ᵥ x = 0 →
      x = ∑ free : balanceGaussianFreeIndex
          (balanceGaussianColumnScan A ∅
            (List.ofFn fun j : Fin n => j)).2,
        x free.1 • balanceGaussianFreeCandidateFamily
          (balanceGaussianColumnScan A ∅
            (List.ofFn fun j : Fin n => j)).1
          (balanceGaussianColumnScan A ∅
            (List.ofFn fun j : Fin n => j)).2 free := by
  classical
  let columns := List.ofFn (fun j : Fin n => j)
  let B := balanceGaussianColumnScan A ∅ columns
  let pivots := B.2
  have hrows : (pivots.map Prod.fst).Nodup := by
    simpa [pivots, B, columns] using
      balanceGaussianColumnScan_pivotRows_nodup columns A ∅
  have hunit : ∀ pivot ∈ pivots, ∀ i,
      B.1 i pivot.2 = if i = pivot.1 then 1 else 0 := by
    intro pivot hpivot i
    exact balanceGaussianColumnScan_recordedPivots_unit
      columns A ∅ pivot hpivot i
  have hzero : ∀ i, i ∉ pivots.map Prod.fst → B.1 i = 0 := by
    intro i hi
    funext column
    exact balanceGaussianFullColumnScan_unusedRows_zero A i hi column
  have hcandidate : ∀ free : balanceGaussianFreeIndex pivots,
      B.1 *ᵥ balanceGaussianFreeCandidateFamily B.1 pivots free = 0 := by
    intro free
    apply balanceGaussianFreeKernelCandidate_mem_ker
      B.1 pivots free.1 free.2 hrows hunit
    intro i hi
    exact congrFun (hzero i hi) free.1
  change ∀ x : Fin n → ZMod 2, B.1 *ᵥ x = 0 →
    x = ∑ free : balanceGaussianFreeIndex pivots,
      x free.1 • balanceGaussianFreeCandidateFamily B.1 pivots free
  exact balanceGaussianFreeCandidateFamily_reconstruct_of_pivotRows
    B.1 pivots hrows hunit hcandidate

end CorruptedFieldRecovery
