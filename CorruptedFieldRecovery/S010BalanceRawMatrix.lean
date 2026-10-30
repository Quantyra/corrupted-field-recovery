import CorruptedFieldRecovery.S010BalanceBasisMatrix
import Mathlib.LinearAlgebra.Matrix.ToLin

open scoped Matrix

namespace CorruptedFieldRecovery

/-- The standard basis of physical endomorphisms, indexed by matrix entries. -/
noncomputable def actualBalanceEndBasis (s : Nat) :
    Module.Basis (Fin (3 * s) × Fin (3 * s)) (ZMod 2)
      (Module.End (ZMod 2) (BinaryVector (3 * s))) :=
  (Pi.basisFun (ZMod 2) (Fin (3 * s))).end

/-- The coefficient matrix of the actual basis-pair balance constraint map.
Rows are the four slots times n^2 basis pairs; columns are n^2 matrix entries
of a candidate endomorphism. -/
noncomputable def actualBalanceRawCoefficientMatrix {s : Nat}
    (A : BinaryTensor (3 * s)) (tape : FiveWordTape s) :
    Matrix (ActualBalanceBasisRow s) (Fin (3 * s) × Fin (3 * s)) (ZMod 2) :=
  LinearMap.toMatrix (actualBalanceEndBasis s)
    (Pi.basisFun (ZMod 2) (ActualBalanceBasisRow s))
    (actualBalanceBasisMatrix A tape)

/-- Coordinates of a physical endomorphism in its standard matrix-unit basis. -/
noncomputable def actualBalanceEndCoordinates {s : Nat}
    (T : Module.End (ZMod 2) (BinaryVector (3 * s))) :
    Fin (3 * s) × Fin (3 * s) → ZMod 2 :=
  fun ij => (actualBalanceEndBasis s).repr T ij

/-- Multiplication by the raw constraint matrix computes all actual balance
residuals in row coordinates. -/
theorem actualBalanceRawMatrix_mulVec_repr {s : Nat}
    (A : BinaryTensor (3 * s)) (tape : FiveWordTape s)
    (T : Module.End (ZMod 2) (BinaryVector (3 * s))) :
    actualBalanceRawCoefficientMatrix A tape *ᵥ
        (actualBalanceEndBasis s).repr T =
      (Pi.basisFun (ZMod 2) (ActualBalanceBasisRow s)).repr
        (actualBalanceBasisMatrix A tape T) := by
  exact LinearMap.toMatrix_mulVec_repr
    (actualBalanceEndBasis s)
    (Pi.basisFun (ZMod 2) (ActualBalanceBasisRow s))
    (actualBalanceBasisMatrix A tape) T

theorem actualBalanceRawMatrix_solution_iff {s : Nat}
    (A : BinaryTensor (3 * s)) (tape : FiveWordTape s)
    (T : Module.End (ZMod 2) (BinaryVector (3 * s))) :
    actualBalanceRawCoefficientMatrix A tape *ᵥ
        (actualBalanceEndBasis s).repr T = 0 ↔
      actualFourBilinearBalanced A tape T := by
  rw [actualBalanceRawMatrix_mulVec_repr]
  constructor
  · intro h
    have hzero : actualBalanceBasisMatrix A tape T = 0 := by
      apply (Pi.basisFun (ZMod 2) (ActualBalanceBasisRow s)).repr.injective
      simpa using h
    exact (actualBalanceBasisMatrix_ker_iff A tape T).1
      (LinearMap.mem_ker.mpr hzero)
  · intro h
    have hker := (actualBalanceBasisMatrix_ker_iff A tape T).2 h
    have hzero : actualBalanceBasisMatrix A tape T = 0 :=
      LinearMap.mem_ker.mp hker
    rw [hzero]
    simp

/-- The matrix itself can be queried coefficient-by-coefficient using the
accepted physical residual map and the standard endomorphism basis. -/
theorem actualBalanceRawCoefficientMatrix_apply {s : Nat}
    (A : BinaryTensor (3 * s)) (tape : FiveWordTape s)
    (row : ActualBalanceBasisRow s) (col : Fin (3 * s) × Fin (3 * s)) :
    actualBalanceRawCoefficientMatrix A tape row col =
      actualBalanceBasisMatrix A tape ((actualBalanceEndBasis s) col) row := by
  rw [actualBalanceRawCoefficientMatrix, LinearMap.toMatrix_apply]
  simp

theorem actualBalanceRawMatrix_solution_iff_check {s : Nat}
    (A : BinaryTensor (3 * s)) (tape : FiveWordTape s)
    (T : Module.End (ZMod 2) (BinaryVector (3 * s))) :
    actualBalanceBasisMatrixCheck A tape T = true ↔
      actualBalanceRawCoefficientMatrix A tape *ᵥ
        (actualBalanceEndBasis s).repr T = 0 := by
  rw [actualBalanceBasisMatrixCheck_iff, actualBalanceBasisMatrix_ker_iff]
  exact (actualBalanceRawMatrix_solution_iff A tape T).symm

end CorruptedFieldRecovery