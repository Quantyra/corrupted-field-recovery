import CorruptedFieldRecovery.S010BalanceGaussianKernelUniqueness

open scoped Matrix

namespace CorruptedFieldRecovery

/-- The explicit free-variable candidates span the kernel of the original input
matrix, not merely the terminal matrix: transport the input kernel equation
through the accepted full-column-scan kernel equivalence, then apply the
scanned-matrix reconstruction theorem. The finite free-index instance is an
explicit proof-level enumeration premise for the displayed sum. -/
theorem balanceGaussianFullColumnScan_candidates_reconstruct_originalKernel
    {m n : Nat} [Fintype (Fin n)]
    (A : Matrix (Fin m) (Fin n) (ZMod 2))
    [Fintype (balanceGaussianFreeIndex
      (balanceGaussianColumnScan A ∅ (List.ofFn fun j : Fin n => j)).2)] :
    ∀ x : Fin n → ZMod 2, A *ᵥ x = 0 →
      x = ∑ free : balanceGaussianFreeIndex
          (balanceGaussianColumnScan A ∅
            (List.ofFn fun j : Fin n => j)).2,
        x free.1 • balanceGaussianFreeCandidateFamily
          (balanceGaussianColumnScan A ∅
            (List.ofFn fun j : Fin n => j)).1
          (balanceGaussianColumnScan A ∅
            (List.ofFn fun j : Fin n => j)).2 free := by
  classical
  intro x hx
  have hscan :
      (balanceGaussianColumnScan A ∅
        (List.ofFn fun j : Fin n => j)).1 *ᵥ x = 0 :=
    (balanceGaussianColumnScan_kernel_iff
      (List.ofFn fun j : Fin n => j) A ∅ x).2 hx
  exact balanceGaussianFullColumnScan_candidates_reconstruct A x hscan

end CorruptedFieldRecovery