import CorruptedFieldRecovery.S010BalanceGaussianArrayOrbitStep
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace CorruptedFieldRecovery

/-! # Array append refinement for an actual operator orbit

This module connects the accepted one-orbit span from
`S010BalanceGaussianArrayOrbitStep` to the concrete `Array.append` used by the
greedy run. It proves the exact column-submodule equality; it does not yet
prove the recursive three-pass success theorem. -/

/-- The ordered family of columns represented by an array. -/
def actualGreedyArrayColumnFamily {m : Nat}
    (columns : Array (Fin m → ZMod 2)) : Fin columns.size → Fin m → ZMod 2 :=
  fun j => columns[j.val]!

/-- The range of a matrix's column map is the span represented by the array. -/
theorem actualGreedyArrayColumnSubmodule_eq_span {m : Nat}
    (columns : Array (Fin m → ZMod 2)) :
    actualGreedyArrayColumnSubmodule columns =
      Submodule.span (ZMod 2)
        (Set.range (actualGreedyArrayColumnFamily columns)) := by
  rw [actualGreedyArrayColumnSubmodule, Matrix.range_mulVecLin]
  rfl

/-- Appending arrays takes the supremum of their represented column spans. -/
theorem actualGreedyArrayAppendColumnSubmodule {m : Nat}
    (left right : Array (Fin m → ZMod 2)) :
    actualGreedyArrayColumnSubmodule (left ++ right) =
      actualGreedyArrayColumnSubmodule left ⊔
        actualGreedyArrayColumnSubmodule right := by
  classical
  let f := actualGreedyArrayColumnFamily left
  let g := actualGreedyArrayColumnFamily right
  have hsize : left.size + right.size = (left ++ right).size :=
    Array.size_append.symm
  let h : Fin (left.size + right.size) → Fin m → ZMod 2 :=
    Fin.addCases (motive := fun _ => Fin m → ZMod 2) f g
  have hfamily : actualGreedyArrayColumnFamily (left ++ right) =
      h ∘ Fin.cast hsize.symm := by
    funext i
    let j : Fin (left.size + right.size) := Fin.cast hsize.symm i
    have hj : Fin.cast hsize j = i := Fin.ext rfl
    rw [← hj]
    simp only [Function.comp_apply]
    induction j using Fin.addCases with
    | left j =>
        have hcast : Fin.cast hsize.symm
            (Fin.cast hsize (Fin.castAdd right.size j)) =
              Fin.castAdd right.size j := Fin.ext rfl
        have heval : h (Fin.cast hsize.symm
            (Fin.cast hsize (Fin.castAdd right.size j))) = f j := by
          rw [hcast]
          simp [h]
        rw [heval]
        have hidx : Fin.cast hsize (Fin.castAdd right.size j) =
            ⟨j.val, by omega⟩ := Fin.ext rfl
        rw [hidx]
        change (left ++ right)[j.val]! = f j
        rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
        rw [Array.getElem?_append_left j.isLt]
        simp [f, actualGreedyArrayColumnFamily]
    | right j =>
        have hcast : Fin.cast hsize.symm
            (Fin.cast hsize (Fin.natAdd left.size j)) =
              Fin.natAdd left.size j := Fin.ext rfl
        have heval : h (Fin.cast hsize.symm
            (Fin.cast hsize (Fin.natAdd left.size j))) = g j := by
          rw [hcast]
          simp [h]
        rw [heval]
        have hidx : Fin.cast hsize (Fin.natAdd left.size j) =
            ⟨left.size + j.val, by omega⟩ := Fin.ext rfl
        rw [hidx]
        change (left ++ right)[left.size + j.val]! = g j
        rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
        rw [Array.getElem?_append_right (show left.size ≤ left.size + j.val by omega)]
        simp [g, actualGreedyArrayColumnFamily]
  have hcastRange : Set.range (actualGreedyArrayColumnFamily (left ++ right)) =
      Set.range (actualGreedyArrayColumnFamily (left ++ right) ∘ Fin.cast hsize) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨Fin.cast hsize.symm i, by simp [Function.comp_apply]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨Fin.cast hsize i, by simp [Function.comp_apply]⟩
  have hcomp : actualGreedyArrayColumnFamily (left ++ right) ∘ Fin.cast hsize = h := by
    rw [hfamily]
    funext i
    simp [Function.comp_apply]
  have hrange : Set.range h =
      Set.range f ∪ Set.range g := by
    ext x
    simp only [Set.mem_range, Set.mem_union]
    constructor
    · rintro ⟨i, rfl⟩
      induction i using Fin.addCases with
      | left j => exact Or.inl ⟨j, by simp [h]⟩
      | right j => exact Or.inr ⟨j, by simp [h]⟩
    · rintro (⟨j, rfl⟩ | ⟨j, rfl⟩)
      · exact ⟨Fin.castAdd right.size j, by simp [h]⟩
      · exact ⟨Fin.natAdd left.size j, by simp [h]⟩
  have hfamilyRange :
      Set.range (actualGreedyArrayColumnFamily (left ++ right)) = Set.range h := by
    rw [hcastRange, hcomp]
  rw [actualGreedyArrayColumnSubmodule_eq_span,
    actualGreedyArrayColumnSubmodule_eq_span,
    actualGreedyArrayColumnSubmodule_eq_span,
    hfamilyRange, hrange, Submodule.span_union]

/-- The actual finite array of the first `s` iterates of `T v`. -/
def actualGreedyArrayOrbitColumns {n s : Nat}
    (T : Module.End (ZMod 2) (BinaryVector n)) (v : BinaryVector n) :
    Array (BinaryVector n) :=
  Array.ofFn (actualGreedyOrbitFamily (s := s) T v)

/-- Reindexing the orbit array's `Fin size` positions back to `Fin s`. -/
def actualGreedyArrayOrbitIndex {n s : Nat}
    (T : Module.End (ZMod 2) (BinaryVector n)) (v : BinaryVector n) :
    Fin (actualGreedyArrayOrbitColumns (s := s) T v).size → Fin s :=
  fun i => ⟨i.val, by simpa [actualGreedyArrayOrbitColumns] using i.isLt⟩

/-- The column family of the orbit array is exactly the specified orbit. -/
theorem actualGreedyArrayOrbitColumns_family {n s : Nat}
    (T : Module.End (ZMod 2) (BinaryVector n)) (v : BinaryVector n) :
    actualGreedyArrayColumnFamily (actualGreedyArrayOrbitColumns (s := s) T v) =
      fun i => actualGreedyOrbitFamily (s := s) T v
        (actualGreedyArrayOrbitIndex (s := s) T v i) := by
  funext i
  change (Array.ofFn (actualGreedyOrbitFamily (s := s) T v))[i.val]! = _
  have hi : i.val < s := by
    simpa [actualGreedyArrayOrbitColumns] using i.isLt
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
  simp [hi, actualGreedyArrayOrbitIndex]

/-- The actual orbit array represents the same submodule as the abstract
finite orbit span. -/
theorem actualGreedyArrayOrbitColumns_span {n s : Nat}
    (T : Module.End (ZMod 2) (BinaryVector n)) (v : BinaryVector n) :
    actualGreedyArrayColumnSubmodule (actualGreedyArrayOrbitColumns (s := s) T v) =
      actualGreedyOrbitSpan (s := s) T v := by
  have hrange :
      Set.range (actualGreedyArrayColumnFamily
        (actualGreedyArrayOrbitColumns (s := s) T v)) =
        Set.range (actualGreedyOrbitFamily (s := s) T v) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨actualGreedyArrayOrbitIndex (s := s) T v i, ?_⟩
      exact (congrFun (actualGreedyArrayOrbitColumns_family T v) i).symm
    · rintro ⟨i, rfl⟩
      refine ⟨⟨i.val, by simp [actualGreedyArrayOrbitColumns]⟩, ?_⟩
      calc
        actualGreedyArrayColumnFamily
            (actualGreedyArrayOrbitColumns (s := s) T v)
            ⟨i.val, by simp [actualGreedyArrayOrbitColumns]⟩ =
          actualGreedyOrbitFamily (s := s) T v
            (actualGreedyArrayOrbitIndex (s := s) T v
              ⟨i.val, by simp [actualGreedyArrayOrbitColumns]⟩) :=
          congrFun (actualGreedyArrayOrbitColumns_family T v) _
        _ = actualGreedyOrbitFamily (s := s) T v i := by
          congr 1
  rw [actualGreedyArrayColumnSubmodule_eq_span, hrange,
    actualGreedyOrbitSpan]

/-- Appending the concrete orbit array has exactly the abstract sup used by
the selected-orbit dimension and invariance theorem. -/
theorem actualGreedyArrayAppendOrbit_span {s : Nat}
    (T : Module.End (ZMod 2) (BinaryVector (3 * s)))
    (columns : Array (BinaryVector (3 * s))) (v : BinaryVector (3 * s)) :
    actualGreedyArrayColumnSubmodule
        (columns ++ actualGreedyArrayOrbitColumns (s := s) T v) =
      actualGreedyArrayColumnSubmodule columns ⊔
        actualGreedyOrbitSpan (s := s) T v := by
  rw [actualGreedyArrayAppendColumnSubmodule,
    actualGreedyArrayOrbitColumns_span]

end CorruptedFieldRecovery
