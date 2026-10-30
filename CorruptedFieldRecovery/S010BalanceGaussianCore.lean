import CorruptedFieldRecovery.S010BalanceRawInputLayout
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

open scoped Matrix

namespace CorruptedFieldRecovery

/-- One Gauss-Jordan pivot operation over F2. It keeps the selected pivot row
and adds the appropriate multiple of it to each other row. -/
def balanceGaussianPivotRow {m n : Nat}
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) (pivotRow : Fin m)
    (pivotColumn : Fin n) : Matrix (Fin m) (Fin n) (ZMod 2) :=
  fun i j => if i = pivotRow then A i j else
    A i j + A i pivotColumn * A pivotRow j

theorem balanceGaussianPivotRow_mulVec_apply {m n : Nat}
    [Fintype (Fin n)]
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) (pivotRow : Fin m)
    (pivotColumn : Fin n) (x : Fin n → ZMod 2) (i : Fin m) :
    (balanceGaussianPivotRow A pivotRow pivotColumn *ᵥ x) i =
      if i = pivotRow then (A *ᵥ x) i else
        (A *ᵥ x) i + A i pivotColumn * ((A *ᵥ x) pivotRow) := by
  by_cases hi : i = pivotRow
  · subst i
    simp [balanceGaussianPivotRow, Matrix.mulVec]
  · have hrow : (fun j : Fin n =>
        A i j + A i pivotColumn * A pivotRow j) =
      (fun j => A i j) + A i pivotColumn • (fun j => A pivotRow j) := by
      funext j
      simp [Pi.add_apply, Pi.smul_apply]
    simp only [balanceGaussianPivotRow, if_neg hi, Matrix.mulVec]
    rw [hrow, add_dotProduct, smul_dotProduct, smul_eq_mul]

theorem balanceGaussianPivotRow_mulVec_zero_iff {m n : Nat}
    [Fintype (Fin n)]
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) (pivotRow : Fin m)
    (pivotColumn : Fin n) (x : Fin n → ZMod 2) :
    balanceGaussianPivotRow A pivotRow pivotColumn *ᵥ x = 0 ↔
      A *ᵥ x = 0 := by
  constructor
  · intro h
    apply funext
    intro i
    by_cases hi : i = pivotRow
    · subst i
      have hp := congrFun h pivotRow
      simpa [balanceGaussianPivotRow_mulVec_apply] using hp
    · have hp : (A *ᵥ x) pivotRow = 0 := by
        have hrow := congrFun h pivotRow
        simpa [balanceGaussianPivotRow_mulVec_apply] using hrow
      have hrow := congrFun h i
      rw [balanceGaussianPivotRow_mulVec_apply, if_neg hi] at hrow
      rw [hp, mul_zero, add_zero] at hrow
      exact hrow
  · intro h
    apply funext
    intro i
    rw [balanceGaussianPivotRow_mulVec_apply, congrFun h i, congrFun h pivotRow]
    simp

/-- Execute a supplied list of Gauss-Jordan pivot-row operations. -/
def balanceGaussianPivotSequence {m n : Nat}
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    List (Fin m × Fin n) → Matrix (Fin m) (Fin n) (ZMod 2)
  | [] => A
  | (pivotRow, pivotColumn) :: steps =>
      balanceGaussianPivotSequence
        (balanceGaussianPivotRow A pivotRow pivotColumn) steps

theorem balanceGaussianPivotSequence_kernel_iff {m n : Nat}
    [Fintype (Fin n)]
    (steps : List (Fin m × Fin n))
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) (x : Fin n → ZMod 2) :
    balanceGaussianPivotSequence A steps *ᵥ x = 0 ↔ A *ᵥ x = 0 := by
  induction steps generalizing A with
  | nil => rfl
  | cons step steps ih =>
      rcases step with ⟨pivotRow, pivotColumn⟩
      exact (ih (balanceGaussianPivotRow A pivotRow pivotColumn)).trans
        (balanceGaussianPivotRow_mulVec_zero_iff A pivotRow pivotColumn x)

end CorruptedFieldRecovery
