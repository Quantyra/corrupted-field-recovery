import CorruptedFieldRecovery.S010BalanceGaussianArrayCandidateInverseProofFixed
import CorruptedFieldRecovery.RawCoordinateEquivalence
import Mathlib.LinearAlgebra.Matrix.ToLin

open scoped Matrix

namespace CorruptedFieldRecovery

/-! # Serialize the actual array-run coordinate inverse

Disjoint uncompiled bridge. It reindexes the two products of the actual
rectangular array/candidate matrices to square physical coordinates, then
serializes those square matrices in the checker's row-major order. The inverse
entries remain the actual free-kernel candidates selected by the array scan.
-/

/-- Reindex the actual array-column matrix to physical square coordinates. -/
def actualGreedyArraySquareForward {m : Nat}
    (columns : Array (BinaryVector m)) (hsize : columns.size = m) :
    Matrix (Fin m) (Fin m) (ZMod 2) :=
  fun row col => actualGreedyArraySpanMatrix columns row
    ((finCongr hsize).symm col)

/-- Reindex coefficient rows of the actual candidate inverse to the same
physical square coordinates. -/
def actualGreedyArraySquareInverse {m : Nat}
    (columns : Array (BinaryVector m)) (hsize : columns.size = m) :
    Matrix (Fin m) (Fin m) (ZMod 2) :=
  fun row col => actualGreedyArrayCandidateInverseMatrix columns
    ((finCongr hsize).symm row) col

/-- The rectangular inverse product identities imply the two square product
identities after the array-position/physical-position reindexing. -/
theorem actualGreedyArraySquareCoordinateMatrices_two_sided
    {m : Nat} (columns : Array (BinaryVector m))
    (hsize : columns.size = m)
    (hleft : actualGreedyArraySpanMatrix columns *
      actualGreedyArrayCandidateInverseMatrix columns = 1)
    (hright : actualGreedyArrayCandidateInverseMatrix columns *
      actualGreedyArraySpanMatrix columns = 1) :
    actualGreedyArraySquareForward columns hsize *
        actualGreedyArraySquareInverse columns hsize = 1 ∧
      actualGreedyArraySquareInverse columns hsize *
        actualGreedyArraySquareForward columns hsize = 1 := by
  let e := finCongr hsize
  let A := actualGreedyArraySpanMatrix columns
  let B := actualGreedyArrayCandidateInverseMatrix columns
  let F := actualGreedyArraySquareForward columns hsize
  let G := actualGreedyArraySquareInverse columns hsize
  have hFG : F * G = 1 := by
    ext row col
    have hsum :
        (∑ j : Fin m, F row j * G j col) =
          ∑ k : Fin columns.size, A row k * B k col := by
      simpa [F, G, A, B, actualGreedyArraySquareForward,
        actualGreedyArraySquareInverse, e] using
        (Equiv.sum_comp e.symm
          (fun k : Fin columns.size => A row k * B k col))
    have hentry := congrFun (congrFun hleft row) col
    calc
      (F * G) row col = ∑ j : Fin m, F row j * G j col := by
        simp [Matrix.mul_apply]
      _ = ∑ k : Fin columns.size, A row k * B k col := hsum
      _ = (A * B) row col := by simp [Matrix.mul_apply]
      _ = (1 : Matrix (Fin m) (Fin m) (ZMod 2)) row col := hentry
  have hGF : G * F = 1 := by
    ext row col
    have hentry := congrFun
      (congrFun hright (e.symm row)) (e.symm col)
    calc
      (G * F) row col = (B * A) (e.symm row) (e.symm col) := by
        simp [Matrix.mul_apply, F, G, A, B,
          actualGreedyArraySquareForward,
          actualGreedyArraySquareInverse, e]
      _ = (1 : Matrix (Fin columns.size) (Fin columns.size) (ZMod 2))
            (e.symm row) (e.symm col) := hentry
      _ = (1 : Matrix (Fin m) (Fin m) (ZMod 2)) row col := by
        have heq : e.symm row = e.symm col ↔ row = col := by
          constructor
          · exact fun hsym => e.symm.injective hsym
          · rintro rfl
            rfl
        simp [Matrix.one_apply, heq]
  exact ⟨hFG, hGF⟩

/-- Row-major serialization of a square finite matrix in the exact offset
order consumed by `rawCoordinateMatrixMap`. -/
def actualGreedyArraySerializeSquareMatrix {n : Nat}
    (A : Matrix (Fin n) (Fin n) (ZMod 2)) : RawCoordinateMatrix :=
  Array.ofFn fun k : Fin (n * n) =>
    let ij := finProdFinEquiv.symm k
    A ij.1 ij.2

/-- The row-major serializer emits exactly `n*n` entries. -/
theorem actualGreedyArraySerializeSquareMatrix_size {n : Nat}
    (A : Matrix (Fin n) (Fin n) (ZMod 2)) :
    (actualGreedyArraySerializeSquareMatrix A).size = n * n := by
  simp [actualGreedyArraySerializeSquareMatrix]

/-- The serialized value at checker offset `(i,j)` is matrix entry `A i j`. -/
theorem actualGreedyArraySerializeSquareMatrix_entry {n : Nat}
    (A : Matrix (Fin n) (Fin n) (ZMod 2)) (i j : Fin n) :
    (actualGreedyArraySerializeSquareMatrix A)[rawCoordinateMatrixOffset n i j]!
      = A i j := by
  classical
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
  have hval : (finProdFinEquiv (i, j)).val =
      rawCoordinateMatrixOffset n i j := by
    simp [rawCoordinateMatrixOffset, finProdFinEquiv]
    ring
  have hbound : (j : Nat) + n * (i : Nat) < n * n := by
    nlinarith [i.isLt, j.isLt]
  have hdiv : ((j : Nat) + n * (i : Nat)) / n = (i : Nat) := by
    rw [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt j.isLt, Nat.zero_add]
  have hmod : ((j : Nat) + n * (i : Nat)) % n = (j : Nat) := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j.isLt]
  rw [← hval, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
  simp [actualGreedyArraySerializeSquareMatrix, hbound, Fin.divNat,
    Fin.modNat, hdiv, hmod]

/-- The raw checker map of a serialized matrix is exactly the finite matrix
vector action. -/
theorem rawCoordinateMatrixMap_actualGreedyArraySerialize_eq_mulVec
    {n : Nat} (A : Matrix (Fin n) (Fin n) (ZMod 2))
    (x : BinaryVector n) :
    rawCoordinateMatrixMap
      (actualGreedyArraySerializeSquareMatrix A) x = A *ᵥ x := by
  ext i
  simp [rawCoordinateMatrixMap, Matrix.mulVec, dotProduct,
    actualGreedyArraySerializeSquareMatrix_entry]

/-- Any two-sided inverse pair serializes to a matrix pair accepted by the
exact raw checker, including its dense-size checks. -/
theorem rawCoordinateMatrixCheck_true_of_actual_array_two_sided
    {n : Nat} (A B : Matrix (Fin n) (Fin n) (ZMod 2))
    (hAB : A * B = 1) (hBA : B * A = 1) :
    rawCoordinateMatrixCheck (n := n)
      (actualGreedyArraySerializeSquareMatrix A)
      (actualGreedyArraySerializeSquareMatrix B) = true := by
  have hleft : ∀ i : Fin n,
      rawCoordinateMatrixMap
        (actualGreedyArraySerializeSquareMatrix B)
        (rawCoordinateMatrixMap
          (actualGreedyArraySerializeSquareMatrix A)
          (rawCoordinateUnitVector i)) = rawCoordinateUnitVector i := by
    intro i
    rw [rawCoordinateMatrixMap_actualGreedyArraySerialize_eq_mulVec,
      rawCoordinateMatrixMap_actualGreedyArraySerialize_eq_mulVec]
    calc
      B *ᵥ (A *ᵥ rawCoordinateUnitVector i) =
          (B * A) *ᵥ rawCoordinateUnitVector i := by
        rw [← Matrix.mulVec_mulVec]
      _ = (1 : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
            rawCoordinateUnitVector i := by rw [hBA]
      _ = rawCoordinateUnitVector i := by simp
  have hright : ∀ i : Fin n,
      rawCoordinateMatrixMap
        (actualGreedyArraySerializeSquareMatrix A)
        (rawCoordinateMatrixMap
          (actualGreedyArraySerializeSquareMatrix B)
          (rawCoordinateUnitVector i)) = rawCoordinateUnitVector i := by
    intro i
    rw [rawCoordinateMatrixMap_actualGreedyArraySerialize_eq_mulVec,
      rawCoordinateMatrixMap_actualGreedyArraySerialize_eq_mulVec]
    calc
      A *ᵥ (B *ᵥ rawCoordinateUnitVector i) =
          (A * B) *ᵥ rawCoordinateUnitVector i := by
        rw [← Matrix.mulVec_mulVec]
      _ = (1 : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ
            rawCoordinateUnitVector i := by rw [hAB]
      _ = rawCoordinateUnitVector i := by simp
  simp [rawCoordinateMatrixCheck, actualGreedyArraySerializeSquareMatrix_size,
    hleft, hright]

/-- Under the explicit monic irreducible annihilator hypotheses, the actual
three-pass output has forward/inverse arrays accepted by the raw coordinate
checker. This remains an uncompiled source-level bridge. -/
theorem actualGreedyArrayOrbitRun_threePass_rawCoordinateCheck
    {s : Nat} (hs : 1 ≤ s)
    (T : Module.End (ZMod 2) (BinaryVector (3 * s)))
    (p : Polynomial (ZMod 2)) (hp : Irreducible p) (hmonic : p.Monic)
    (hdeg : p.natDegree = s) (hroot : Polynomial.aeval T p = 0) :
    ∃ outColumns outSelected,
      actualGreedyArrayOrbitRun T 3
        (#[] : Array (BinaryVector (3 * s))) #[] =
          some (outColumns, outSelected) ∧
      ∃ (houtColumnsSize : outColumns.size = 3 * s),
      rawCoordinateMatrixCheck (n := 3 * s)
        (actualGreedyArraySerializeSquareMatrix
          (actualGreedyArraySquareForward outColumns houtColumnsSize))
        (actualGreedyArraySerializeSquareMatrix
          (actualGreedyArraySquareInverse outColumns houtColumnsSize)) = true := by
  obtain ⟨outColumns, outSelected, hrun, houtColumnsSize, hleft, hright⟩ :=
    actualGreedyArrayOrbitRun_threePass_candidateInverse_two_sided
      hs T p hp hmonic hdeg hroot
  have hsquare := actualGreedyArraySquareCoordinateMatrices_two_sided
    outColumns houtColumnsSize hleft hright
  refine ⟨outColumns, outSelected, hrun, houtColumnsSize, ?_⟩
  exact rawCoordinateMatrixCheck_true_of_actual_array_two_sided
    (actualGreedyArraySquareForward outColumns houtColumnsSize)
    (actualGreedyArraySquareInverse outColumns houtColumnsSize)
    hsquare.1 hsquare.2

end CorruptedFieldRecovery
