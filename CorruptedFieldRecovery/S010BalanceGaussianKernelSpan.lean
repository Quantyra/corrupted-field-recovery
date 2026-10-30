import CorruptedFieldRecovery.S010BalanceGaussianKernelProof
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

open scoped Matrix

namespace CorruptedFieldRecovery

/-- Index type of the free columns of a recorded pivot list. -/
def balanceGaussianFreeIndex {m n : Nat} (pivots : List (Fin m × Fin n)) :=
  {column : Fin n // column ∉ pivots.map Prod.snd}

/-- The concrete free-variable candidate family indexed by nonpivot columns. -/
def balanceGaussianFreeCandidateFamily {m n : Nat}
    (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (pivots : List (Fin m × Fin n)) :
    balanceGaussianFreeIndex pivots → Fin n → ZMod 2 :=
  fun free => balanceGaussianFreeKernelCandidate A pivots free.1

theorem balanceGaussianFreeCandidateFamily_coordinate_identity
    {m n : Nat} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (pivots : List (Fin m × Fin n))
    [DecidableEq (balanceGaussianFreeIndex pivots)]
    (free column : balanceGaussianFreeIndex pivots) :
    balanceGaussianFreeCandidateFamily A pivots free column.1 =
      if column = free then 1 else 0 := by
  classical
  have h := balanceGaussianFreeKernelCandidate_apply_freeColumn
    A pivots free.1 column.1 column.2
  by_cases heq : column = free
  · subst column
    simpa [balanceGaussianFreeCandidateFamily] using h
  · have hval : column.1 ≠ free.1 := by
      intro hvalue
      exact heq (Subtype.ext hvalue)
    simpa [balanceGaussianFreeCandidateFamily, heq, hval] using h

/-- Identity coordinates on the free columns give linear independence. -/
theorem balanceGaussianFreeCandidateFamily_linearIndependent
    {m n : Nat} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (pivots : List (Fin m × Fin n))
    [Fintype (balanceGaussianFreeIndex pivots)]
    [DecidableEq (balanceGaussianFreeIndex pivots)] :
    LinearIndependent (ZMod 2) (balanceGaussianFreeCandidateFamily A pivots) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro coeff hsum free
  have h := congrFun hsum free.1
  simpa [Finset.sum_apply,
    balanceGaussianFreeCandidateFamily_coordinate_identity] using h

/-- If every candidate is in the kernel and the pivot-row equations imply
that a kernel vector is determined by its free coordinates, then the explicit
free-variable candidates span the kernel. The equality is constructive: the
coefficient of each candidate is the corresponding free coordinate. -/
theorem balanceGaussianFreeCandidateFamily_reconstruct
    {m n : Nat} [Fintype (Fin n)]
    (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (pivots : List (Fin m × Fin n))
    [Fintype (balanceGaussianFreeIndex pivots)]
    (hker : ∀ free : balanceGaussianFreeIndex pivots,
      A *ᵥ balanceGaussianFreeCandidateFamily A pivots free = 0)
    (hunique : ∀ x : Fin n → ZMod 2,
      A *ᵥ x = 0 →
        (∀ free : balanceGaussianFreeIndex pivots, x free.1 = 0) → x = 0) :
    ∀ x : Fin n → ZMod 2, A *ᵥ x = 0 →
      x = ∑ free : balanceGaussianFreeIndex pivots,
        x free.1 • balanceGaussianFreeCandidateFamily A pivots free := by
  classical
  intro x hx
  let y := ∑ free : balanceGaussianFreeIndex pivots,
    x free.1 • balanceGaussianFreeCandidateFamily A pivots free
  let L : (Fin n → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) :=
    Matrix.mulVecBilin (ZMod 2) (ZMod 2) A
  have hyL : L y = 0 := by
    dsimp [y]
    rw [map_sum]
    simp [L, Matrix.mulVecBilin_apply, hker]
  have hy : A *ᵥ y = 0 := by
    simpa [L, Matrix.mulVecBilin_apply] using hyL
  have hycoord : ∀ free : balanceGaussianFreeIndex pivots,
      y free.1 = x free.1 := by
    intro free
    simp [y, Finset.sum_apply,
      balanceGaussianFreeCandidateFamily_coordinate_identity]
  have hdiff : A *ᵥ (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hx, hy]
    simp
  have hdiffFree : ∀ free : balanceGaussianFreeIndex pivots,
      (x - y) free.1 = 0 := by
    intro free
    simp [Pi.sub_apply, hycoord free]
  have hzero := hunique (x - y) hdiff hdiffFree
  exact sub_eq_zero.mp hzero

end CorruptedFieldRecovery
