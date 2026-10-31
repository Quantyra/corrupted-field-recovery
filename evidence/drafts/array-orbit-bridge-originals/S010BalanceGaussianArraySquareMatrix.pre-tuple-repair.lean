import CorruptedFieldRecovery.S010BalanceGaussianArrayOrbitRun
import Mathlib.LinearAlgebra.Matrix.ToLin

namespace CorruptedFieldRecovery

/-! # Square matrix view of the actual greedy array

Disjoint uncompiled bridge. The coordinate inverse and serialization drafts
currently use a separate legacy `RawGreedyOrbitState` path. This module builds
a square matrix directly from the returned array of the accepted three-pass
run and proves its columns span the physical space. It does not yet construct
the inverse or serialize a certificate.
-/

/-- The square matrix read from an array whose length is the coordinate
 dimension. The entry function is directly executable array lookup. -/
def actualGreedyArraySquareMatrix {m : Nat}
    (columns : Array (BinaryVector m)) : Matrix (Fin m) (Fin m) (ZMod 2) :=
  fun row column => columns[column.val]! row

/-- Reindexing the square matrix columns by the array positions recovers the
array's exact ordered column family. -/
theorem actualGreedyArraySquareMatrix_colFamily {m : Nat}
    (columns : Array (BinaryVector m)) (hsize : columns.size = m) :
    (actualGreedyArraySquareMatrix columns).col =
      actualGreedyArrayColumnFamily columns ∘ Fin.cast hsize.symm := by
  funext column row
  rfl

/-- The square matrix and array have the same set of columns whenever the
array length equals its coordinate dimension. -/
theorem actualGreedyArraySquareMatrix_colRange {m : Nat}
    (columns : Array (BinaryVector m)) (hsize : columns.size = m) :
    Set.range (actualGreedyArraySquareMatrix columns).col =
      Set.range (actualGreedyArrayColumnFamily columns) := by
  have hfamily := actualGreedyArraySquareMatrix_colFamily columns hsize
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨Fin.cast hsize.symm j, (congrFun hfamily j).symm⟩
  · rintro ⟨i, rfl⟩
    refine ⟨Fin.cast hsize i, ?_⟩
    rw [hfamily]
    simp

/-- Full span of an array is equivalently full column span of its square
matrix view, when its exact length is known. -/
theorem actualGreedyArraySquareMatrix_span_eq_top_of_array_top {m : Nat}
    (columns : Array (BinaryVector m)) (hsize : columns.size = m)
    (hspan : actualGreedyArrayColumnSubmodule columns = ⊤) :
    Submodule.span (ZMod 2)
      (Set.range (actualGreedyArraySquareMatrix columns).col) = ⊤ := by
  have harray : Submodule.span (ZMod 2)
      (Set.range (actualGreedyArrayColumnFamily columns)) = ⊤ := by
    rw [← actualGreedyArrayColumnSubmodule_eq_span]
    exact hspan
  rw [actualGreedyArraySquareMatrix_colRange columns hsize]
  exact harray

/-- The accepted three-pass run returns an actual square matrix whose columns
span the whole physical space. The hypotheses are the explicit annihilator
conditions used to prove each greedy pass succeeds. -/
theorem actualGreedyArrayOrbitRun_threePass_squareMatrix_span
    {s : Nat} (hs : 1 ≤ s)
    (T : Module.End (ZMod 2) (BinaryVector (3 * s)))
    (p : Polynomial (ZMod 2)) (hp : Irreducible p) (hmonic : p.Monic)
    (hdeg : p.natDegree = s) (hroot : Polynomial.aeval T p = 0) :
    ∃ outColumns outSelected,
      actualGreedyArrayOrbitRun T 3
        (#[] : Array (BinaryVector (3 * s))) #[] =
          some (outColumns, outSelected) ∧
      outColumns.size = 3 * s ∧
      Submodule.span (ZMod 2)
        (Set.range (actualGreedyArraySquareMatrix outColumns).col) = ⊤ := by
  obtain ⟨outColumns, outSelected, outSpan, hrun, houtSpan, houtDim,
      _, _, _, houtColumnsSize⟩ :=
    actualGreedyArrayOrbitRun_threePass hs T p hp hmonic hdeg hroot
  have houtColumnsTop : actualGreedyArrayColumnSubmodule outColumns = ⊤ := by
    rw [houtSpan]
    apply Submodule.eq_top_of_finrank_eq
    simpa [BinaryVector, finrank_pi] using houtDim
  refine ⟨outColumns, outSelected, hrun, houtColumnsSize, ?_⟩
  exact actualGreedyArraySquareMatrix_span_eq_top_of_array_top
    outColumns houtColumnsSize houtColumnsTop

end CorruptedFieldRecovery
