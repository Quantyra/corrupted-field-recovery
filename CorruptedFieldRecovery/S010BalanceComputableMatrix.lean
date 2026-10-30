import CorruptedFieldRecovery.S010BalanceRawMatrix
import Mathlib.Tactic

open scoped Matrix

namespace CorruptedFieldRecovery

/-- A computable matrix unit sending coordinate q to coordinate p. -/
def actualBalanceMatrixUnitEnd {n : Nat} (p q : Fin n) :
    Module.End (ZMod 2) (BinaryVector n) where
  toFun x := fun i => if i = p then x q else 0
  map_add' x y := by
    funext i
    by_cases h : i = p <;> simp [h]
  map_smul' a x := by
    funext i
    by_cases h : i = p <;> simp [h]

/-- The coefficient of a candidate physical endomorphism at matrix position
(p,q), computed by applying it to the q-th coordinate vector. -/
def actualBalanceMatrixEntry {n : Nat}
    (T : Module.End (ZMod 2) (BinaryVector n)) (p q : Fin n) : ZMod 2 :=
  T (actualBalanceUnitVector q) p

/-- The computable coefficient matrix: each entry is the actual physical
balance residual evaluated on a computable matrix-unit endomorphism. -/
def actualBalanceComputableCoefficientMatrix {s : Nat}
    (A : BinaryTensor (3 * s)) (tape : FiveWordTape s) :
    Matrix (ActualBalanceBasisRow s) (Fin (3 * s) × Fin (3 * s)) (ZMod 2) :=
  fun row col =>
    actualBalanceBasisResidual A tape
      (actualBalanceMatrixUnitEnd col.1 col.2) row

/-- The concrete matrix units coincide with the standard endomorphism basis
used in the semantic raw-matrix theorem. -/
theorem actualBalanceMatrixUnitEnd_eq_basis {s : Nat}
    (p q : Fin (3 * s)) :
    actualBalanceMatrixUnitEnd p q = actualBalanceEndBasis s (p, q) := by
  apply (Pi.basisFun (ZMod 2) (Fin (3 * s))).ext
  intro j
  funext i
  rw [actualBalanceEndBasis, Module.Basis.end_apply_apply]
  by_cases hi : i = p <;> by_cases hq : q = j <;>
    simp [actualBalanceMatrixUnitEnd, hi, hq]

/-- The executable coefficients agree entrywise with the semantic basis
matrix. -/
theorem actualBalanceComputableCoefficientMatrix_eq_raw {s : Nat}
    (A : BinaryTensor (3 * s)) (tape : FiveWordTape s) :
    actualBalanceComputableCoefficientMatrix A tape =
      actualBalanceRawCoefficientMatrix A tape := by
  ext row col
  rw [actualBalanceComputableCoefficientMatrix,
    actualBalanceRawCoefficientMatrix_apply,
    actualBalanceMatrixUnitEnd_eq_basis]
  simp [actualBalanceBasisMatrix, actualBalanceBasisResidual]

/-- The raw matrix can be multiplied by the explicit endomorphism-entry vector
to compute every coefficient residual. This is the executable matrix equation
that the Gaussian elimination routine will consume. -/
theorem actualBalanceComputableMatrix_mulVec_residuals {s : Nat}
    (A : BinaryTensor (3 * s)) (tape : FiveWordTape s)
    (T : Module.End (ZMod 2) (BinaryVector (3 * s))) :
    actualBalanceComputableCoefficientMatrix A tape *ᵥ
        (actualBalanceEndBasis s).repr T =
      fun row => actualBalanceBasisResidual A tape T row := by
  rw [actualBalanceComputableCoefficientMatrix_eq_raw,
    actualBalanceRawMatrix_mulVec_repr]
  funext row
  simp [actualBalanceBasisMatrix, actualBalanceBasisResidual]

/-- Explicit row-major coordinate enumeration for the finite matrix serializer. -/
def actualBalanceCoordinateList (n : Nat) : List (Fin n) :=
  List.ofFn fun i : Fin n => i

def actualBalanceRowList (s : Nat) : List (ActualBalanceBasisRow s) :=
  (List.ofFn fun i : Fin 4 => i).flatMap fun i =>
    (actualBalanceCoordinateList (3 * s)).flatMap fun j =>
      (actualBalanceCoordinateList (3 * s)).map fun k => (i, j, k)

def actualBalanceColumnList (s : Nat) : List (Fin (3 * s) × Fin (3 * s)) :=
  (actualBalanceCoordinateList (3 * s)).flatMap fun p =>
    (actualBalanceCoordinateList (3 * s)).map fun q => (p, q)

/-- Row-major serialized coefficient table for direct finite-array use. The
array is built from the actual tensor contractions and contains no
noncomputable basis coordinates. -/
def actualBalanceSerializedCoefficientMatrix {s : Nat}
    (A : BinaryTensor (3 * s)) (tape : FiveWordTape s) :
    Array (Array (ZMod 2)) :=
  ((actualBalanceRowList s).map fun row =>
    ((actualBalanceColumnList s).map fun col =>
      actualBalanceComputableCoefficientMatrix A tape row col).toArray).toArray

@[simp] theorem actualBalanceSerializedCoefficientMatrix_size {s : Nat}
    (A : BinaryTensor (3 * s)) (tape : FiveWordTape s) :
    (actualBalanceSerializedCoefficientMatrix A tape).size =
      (actualBalanceRowList s).length := by
  simp [actualBalanceSerializedCoefficientMatrix]

end CorruptedFieldRecovery