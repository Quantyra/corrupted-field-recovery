import CorruptedFieldRecovery.S010BalanceGaussianArrayDeterministicScan

open scoped Matrix

namespace CorruptedFieldRecovery

/-! A generic bridge from the actual nested-array column scan to the kernel of
the input array's matrix view. This is intended as the clean base for an
array-backed greedy span-membership test. It does not yet decide column-span
membership or construct the greedy orbit basis. -/

/-- For any rectangular nested array and any supplied column order, the
kernel of the array scan's final matrix view equals the kernel of its input
view. The proof composes the accepted array-to-matrix scan refinement with
the matrix scan's row-operation kernel invariant. -/
theorem actualBalanceGaussianArrayColumnScan_kernel_iff
    {m n : Nat} [Fintype (Fin n)]
    (cells : Array (Array (ZMod 2))) (used : Finset (Fin m))
    (columns : List (Fin n)) (x : Fin n → ZMod 2) :
    actualBalanceGaussianArrayView
        (m := m) (n := n)
        (actualBalanceGaussianArrayColumnScan cells used columns).1 *ᵥ x = 0 ↔
      actualBalanceGaussianArrayView (m := m) (n := n) cells *ᵥ x = 0 := by
  have hscan := actualBalanceGaussianArrayColumnScan_refines cells used columns
  have hmatrix :
      actualBalanceGaussianArrayView (m := m) (n := n)
          (actualBalanceGaussianArrayColumnScan (m := m) (n := n)
            cells used columns).1 =
        (balanceGaussianColumnScan
          (actualBalanceGaussianArrayView (m := m) (n := n) cells)
          used columns).1 := by
    simpa using congrArg Prod.fst hscan
  rw [hmatrix]
  exact balanceGaussianColumnScan_kernel_iff columns
    (actualBalanceGaussianArrayView (m := m) (n := n) cells) used x

/-- The full left-to-right scan through every column also preserves the
input kernel. This is the form used by augmented systems in the greedy
selector. -/
theorem actualBalanceGaussianArrayFullColumnScan_kernel_iff
    {m n : Nat} [Fintype (Fin n)]
    (cells : Array (Array (ZMod 2))) (x : Fin n → ZMod 2) :
    actualBalanceGaussianArrayView
        (m := m) (n := n)
        (actualBalanceGaussianArrayColumnScan (m := m) (n := n) cells ∅
          (List.ofFn fun column : Fin n => column)).1 *ᵥ x = 0 ↔
      actualBalanceGaussianArrayView (m := m) (n := n) cells *ᵥ x = 0 := by
  exact actualBalanceGaussianArrayColumnScan_kernel_iff (m := m) (n := n) cells ∅
    (List.ofFn fun column : Fin n => column) x

end CorruptedFieldRecovery
