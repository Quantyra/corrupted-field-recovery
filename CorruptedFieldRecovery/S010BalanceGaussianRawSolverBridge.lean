import CorruptedFieldRecovery.S010BalanceGaussianKernelUniqueness
import CorruptedFieldRecovery.S010BalanceRawInputMatrix
import Mathlib.Tactic

open scoped Matrix

namespace CorruptedFieldRecovery

/-- Row reindexing from the four physical slots times two coordinates to a
finite row number. The equivalence is built from `finProdFinEquiv`, so it is
computable and follows the declared product order. -/
def actualBalanceGaussianRowEquiv (s : Nat) :
    ActualBalanceBasisRow s ≃ Fin (4 * ((3 * s) * (3 * s))) :=
  (Equiv.prodCongr (Equiv.refl (Fin 4))
    (finProdFinEquiv :
      (Fin (3 * s) × Fin (3 * s)) ≃ Fin ((3 * s) * (3 * s)))).trans
    (finProdFinEquiv :
      (Fin 4 × Fin ((3 * s) * (3 * s))) ≃
        Fin (4 * ((3 * s) * (3 * s))))

/-- Column reindexing from a pair of physical matrix coordinates to a finite
column number. -/
def actualBalanceGaussianColumnEquiv (s : Nat) :
    (Fin (3 * s) × Fin (3 * s)) ≃ Fin ((3 * s) * (3 * s)) :=
  finProdFinEquiv

/-- The raw balance coefficient matrix reindexed to the `Fin` indices consumed
by the executable Gaussian scan. It is computed from the supplied raw array
through the existing decoder and contraction coefficient builder. -/
def actualBalanceGaussianRawMatrix {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s) :
    Matrix (Fin (4 * ((3 * s) * (3 * s))))
      (Fin ((3 * s) * (3 * s))) (ZMod 2) :=
  Matrix.reindex (actualBalanceGaussianRowEquiv s)
    (actualBalanceGaussianColumnEquiv s)
    (actualBalanceRawInputCoefficientMatrix raw tape)

/-- Computable coordinates of an endomorphism in row-major matrix-entry order,
reindexed to the finite columns used by the solver. -/
def actualBalanceGaussianInputCoordinates {s : Nat}
    (T : Module.End (ZMod 2) (BinaryVector (3 * s))) :
    Fin ((3 * s) * (3 * s)) → ZMod 2 :=
  fun column =>
    actualBalanceMatrixEntry T
      ((actualBalanceGaussianColumnEquiv s).symm column).1
      ((actualBalanceGaussianColumnEquiv s).symm column).2

/-- The finite coordinate vector agrees with the standard endomorphism-basis
coordinates after applying the explicit product equivalence. -/
theorem actualBalanceGaussianInputCoordinates_pair {s : Nat}
    (T : Module.End (ZMod 2) (BinaryVector (3 * s))) :
    (fun pair => actualBalanceGaussianInputCoordinates T
      (actualBalanceGaussianColumnEquiv s pair)) =
      (actualBalanceEndBasis s).repr T := by
  funext pair
  simp [actualBalanceGaussianInputCoordinates, actualBalanceMatrixEntry,
    coordinateVector, actualBalanceEndBasis, Matrix.stdBasis,
    actualBalanceUnitVector_eq_coordinateVector]

/-- Multiplication by the reindexed finite matrix is exactly the original raw
matrix residual vector transported through the row equivalence. -/
theorem actualBalanceGaussianRawMatrix_mulVec_eq_reindexed
    {s : Nat} (raw : RawCoefficientArray) (tape : FiveWordTape s)
    (x : Fin ((3 * s) * (3 * s)) → ZMod 2) :
    actualBalanceGaussianRawMatrix raw tape *ᵥ x =
      (fun row =>
        (actualBalanceRawInputCoefficientMatrix raw tape *ᵥ
          (fun pair => x (actualBalanceGaussianColumnEquiv s pair)))
          ((actualBalanceGaussianRowEquiv s).symm row)) := by
  classical
  funext row
  simp only [actualBalanceGaussianRawMatrix, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.mulVec, dotProduct]
  simpa only [Equiv.apply_symm_apply] using
    (Equiv.sum_comp (actualBalanceGaussianColumnEquiv s).symm
      (fun pair : Fin (3 * s) × Fin (3 * s) =>
        actualBalanceRawInputCoefficientMatrix raw tape
          ((actualBalanceGaussianRowEquiv s).symm row) pair *
          x (actualBalanceGaussianColumnEquiv s pair)))

/-- The complete finite solver system is equivalent to the manuscript's
physical balance equations for the decoded raw input. -/
theorem actualBalanceGaussianRawMatrix_solution_iff
    {s : Nat} (raw : RawCoefficientArray) (tape : FiveWordTape s)
    (T : Module.End (ZMod 2) (BinaryVector (3 * s))) :
    actualBalanceGaussianRawMatrix raw tape *ᵥ
        actualBalanceGaussianInputCoordinates T = 0 ↔
      actualFourBilinearBalanced (decodeRawArray (n := 3 * s) raw) tape T := by
  rw [actualBalanceGaussianRawMatrix_mulVec_eq_reindexed]
  have hcoords :
      (fun pair => actualBalanceGaussianInputCoordinates T
        (actualBalanceGaussianColumnEquiv s pair)) =
        (actualBalanceEndBasis s).repr T :=
    actualBalanceGaussianInputCoordinates_pair T
  have hmatrix : actualBalanceRawInputCoefficientMatrix raw tape =
      actualBalanceRawCoefficientMatrix
        (decodeRawArray (n := 3 * s) raw) tape := by
    rw [actualBalanceRawInputCoefficientMatrix,
      actualBalanceComputableCoefficientMatrix_eq_raw]
  constructor
  · intro h
    have hpair : actualBalanceRawInputCoefficientMatrix raw tape *ᵥ
        (actualBalanceEndBasis s).repr T = 0 := by
      apply funext
      intro pair
      have hr := congrFun h (actualBalanceGaussianRowEquiv s pair)
      simpa [hcoords] using hr
    rw [hmatrix] at hpair
    exact (actualBalanceRawMatrix_solution_iff
      (decodeRawArray (n := 3 * s) raw) tape T).mp hpair
  · intro h
    have hpair : actualBalanceRawInputCoefficientMatrix raw tape *ᵥ
        (actualBalanceEndBasis s).repr T = 0 := by
      rw [hmatrix]
      exact (actualBalanceRawMatrix_solution_iff
        (decodeRawArray (n := 3 * s) raw) tape T).mpr h
    apply funext
    intro row
    have hr := congrFun hpair ((actualBalanceGaussianRowEquiv s).symm row)
    simpa [hcoords] using hr

/-- Deterministic elimination run on the actual reindexed raw balance matrix.
The result contains the reduced matrix and the ordered pivot-row/column
certificate used to build free-variable kernel candidates. -/
def actualBalanceGaussianRawScan {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s) :=
  balanceGaussianColumnScan (actualBalanceGaussianRawMatrix raw tape) ∅
    (List.ofFn fun column : Fin ((3 * s) * (3 * s)) => column)

/-- Executable list of free columns selected as the complement of the actual
scan's recorded pivot columns. -/
def actualBalanceGaussianRawFreeColumns {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s) :
    List (Fin ((3 * s) * (3 * s))) :=
  let run := actualBalanceGaussianRawScan raw tape
  (List.ofFn fun column : Fin ((3 * s) * (3 * s)) => column).filter
    (fun column => decide (column ∉ run.2.map Prod.snd))

/-- Executable candidate kernel vectors, one for each free column of the
deterministic scan. -/
def actualBalanceGaussianRawKernelCandidates {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s) :
    List (Fin ((3 * s) * (3 * s)) → ZMod 2) :=
  let run := actualBalanceGaussianRawScan raw tape
  (actualBalanceGaussianRawFreeColumns raw tape).map
    (balanceGaussianFreeKernelCandidate run.1 run.2)

/-- A vanishing raw balance check for the reindexed finite matrix has exactly
the physical meaning of four-slot balance, subject to the raw input's declared
length condition. -/
theorem actualBalanceGaussianRawCheck_iff
    {s : Nat} (raw : RawCoefficientArray) (tape : FiveWordTape s)
    (T : Module.End (ZMod 2) (BinaryVector (3 * s)))
    (hsize : raw.size = (3 * s) * (3 * s) * (3 * s)) :
    actualBalanceGaussianRawMatrix raw tape *ᵥ
        actualBalanceGaussianInputCoordinates T = 0 ↔
      actualBalanceRawInputConstraintCheck raw tape T = true := by
  rw [actualBalanceGaussianRawMatrix_solution_iff]
  rw [actualBalanceRawInputConstraintCheck_iff]
  simp [hsize]

end CorruptedFieldRecovery
