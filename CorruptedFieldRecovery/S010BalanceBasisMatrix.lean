import CorruptedFieldRecovery.S010ObservedHiddenBalance
import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.LinearAlgebra.BilinearForm.Hom
import Mathlib.Tactic

namespace CorruptedFieldRecovery

/-- The n^2 coefficient rows for four actual physical balance forms. -/
abbrev ActualBalanceBasisRow (s : Nat) := Fin 4 × Fin (3 * s) × Fin (3 * s)

/-- A computable standard coordinate vector, written directly as a function. -/
def actualBalanceUnitVector {n : Nat} (j : Fin n) : BinaryVector n :=
  fun k => if k = j then 1 else 0

theorem actualBalanceUnitVector_eq_coordinateVector {n : Nat} (j : Fin n) :
    actualBalanceUnitVector j = coordinateVector j := by
  funext k
  by_cases h : k = j <;>
    simp [actualBalanceUnitVector, coordinateVector, Pi.basisFun,
      h]

/-- The row residual of the balance matrix on standard coordinate vectors. -/
def actualBalanceBasisResidual {s : Nat}
    (A : BinaryTensor (3 * s)) (tape : FiveWordTape s)
    (T : Module.End (ZMod 2) (BinaryVector (3 * s)))
    (row : ActualBalanceBasisRow s) : ZMod 2 :=
  let (i, j, k) := row
  physicalThirdSlotBilinForm A (tape.1 i)
      (T (actualBalanceUnitVector j)) (actualBalanceUnitVector k) -
    physicalThirdSlotBilinForm A (tape.1 i)
      (actualBalanceUnitVector j) (T (actualBalanceUnitVector k))

/-- The finite n^2-per-slot balance matrix as a linear map from candidate
physical endomorphisms to coefficient residuals. -/
def actualBalanceBasisMatrix {s : Nat}
    (A : BinaryTensor (3 * s)) (tape : FiveWordTape s) :
    Module.End (ZMod 2) (BinaryVector (3 * s)) →ₗ[ZMod 2]
      (ActualBalanceBasisRow s → ZMod 2) where
  toFun T := fun row => actualBalanceBasisResidual A tape T row
  map_add' T S := by
    funext row
    rcases row with ⟨i, j, k⟩
    simp [actualBalanceBasisResidual, physicalThirdSlotBilinForm, map_add]
    ring
  map_smul' a T := by
    funext row
    rcases row with ⟨i, j, k⟩
    simp [actualBalanceBasisResidual, physicalThirdSlotBilinForm, map_smul]
    ring

@[simp] theorem actualBalanceBasisMatrix_apply {s : Nat}
    (A : BinaryTensor (3 * s)) (tape : FiveWordTape s)
    (T : Module.End (ZMod 2) (BinaryVector (3 * s)))
    (i : Fin 4) (j k : Fin (3 * s)) :
    actualBalanceBasisMatrix A tape T (i, j, k) =
      physicalThirdSlotBilinForm A (tape.1 i)
        (T (actualBalanceUnitVector j)) (actualBalanceUnitVector k) -
      physicalThirdSlotBilinForm A (tape.1 i)
        (actualBalanceUnitVector j) (T (actualBalanceUnitVector k)) := rfl

/-- The n^2-per-slot coefficient matrix vanishes exactly when the complete
physical bilinear balance equations hold for arbitrary x and y. -/
theorem actualBalanceBasisMatrix_ker_iff {s : Nat}
    (A : BinaryTensor (3 * s)) (tape : FiveWordTape s)
    (T : Module.End (ZMod 2) (BinaryVector (3 * s))) :
    T ∈ LinearMap.ker (actualBalanceBasisMatrix A tape) ↔
      actualFourBilinearBalanced A tape T := by
  constructor
  · intro h i x y
    have hzero : actualBalanceBasisMatrix A tape T = 0 :=
      LinearMap.mem_ker.mp h
    -- The row constraints extend bilinearly from the coordinate basis.
    have hrowAll (j k : Fin (3 * s)) :
        physicalThirdSlotBilinForm A (tape.1 i)
          (T (coordinateVector j)) (coordinateVector k) =
        physicalThirdSlotBilinForm A (tape.1 i)
          (coordinateVector j) (T (coordinateVector k)) := by
      have hz := congrFun hzero (i, j, k)
      rw [actualBalanceBasisMatrix_apply] at hz
      have hj := actualBalanceUnitVector_eq_coordinateVector j
      have hk := actualBalanceUnitVector_eq_coordinateVector k
      rw [hj, hk] at hz
      exact sub_eq_zero.mp hz
    let B := physicalThirdSlotBilinForm A (tape.1 i)
    have hforms : B.compLeft T = B.compRight T := by
      apply LinearMap.ext_basis
        (Pi.basisFun (ZMod 2) (Fin (3 * s)))
        (Pi.basisFun (ZMod 2) (Fin (3 * s)))
      intro j k
      rw [LinearMap.BilinForm.compLeft_apply,
        LinearMap.BilinForm.compRight_apply]
      exact hrowAll j k
    have hxy := congrArg (fun F : LinearMap.BilinForm (ZMod 2)
      (BinaryVector (3 * s)) => F x y) hforms
    simpa [B, LinearMap.BilinForm.compLeft_apply,
      LinearMap.BilinForm.compRight_apply] using hxy
  · intro h
    apply LinearMap.mem_ker.mpr
    apply funext
    intro row
    rcases row with ⟨i, j, k⟩
    rw [actualBalanceBasisMatrix_apply]
    have hxy := h i (coordinateVector j) (coordinateVector k)
    have hj := actualBalanceUnitVector_eq_coordinateVector j
    have hk := actualBalanceUnitVector_eq_coordinateVector k
    rw [← hj, ← hk] at hxy
    exact sub_eq_zero.mpr hxy

theorem actualBalanceBasisRow_card {s : Nat} :
    Fintype.card (ActualBalanceBasisRow s) = 4 * (3 * s) * (3 * s) := by
  simp [ActualBalanceBasisRow, Nat.mul_assoc]

/-- Executable finite check of the n^2-per-slot matrix on a supplied physical
endomorphism. -/
def actualBalanceBasisMatrixCheck {s : Nat}
    (A : BinaryTensor (3 * s)) (tape : FiveWordTape s)
    (T : Module.End (ZMod 2) (BinaryVector (3 * s))) : Bool :=
  decide (∀ row : ActualBalanceBasisRow s,
    actualBalanceBasisResidual A tape T row = 0)

theorem actualBalanceBasisMatrixCheck_iff {s : Nat}
    (A : BinaryTensor (3 * s)) (tape : FiveWordTape s)
    (T : Module.End (ZMod 2) (BinaryVector (3 * s))) :
    actualBalanceBasisMatrixCheck A tape T = true ↔
      T ∈ LinearMap.ker (actualBalanceBasisMatrix A tape) := by
  rw [actualBalanceBasisMatrixCheck, decide_eq_true_iff]
  constructor
  · intro h
    apply LinearMap.mem_ker.mpr
    apply funext
    intro row
    simpa [actualBalanceBasisMatrix, actualBalanceBasisResidual] using h row
  · intro h row
    have hzero : actualBalanceBasisMatrix A tape T = 0 :=
      LinearMap.mem_ker.mp h
    simpa [actualBalanceBasisMatrix, actualBalanceBasisResidual] using congrFun hzero row

end CorruptedFieldRecovery