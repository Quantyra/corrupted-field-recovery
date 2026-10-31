import CorruptedFieldRecovery.S010BalanceGaussianArrayGreedySpan
import CorruptedFieldRecovery.S010BalanceGaussianArrayOrbitRun

namespace CorruptedFieldRecovery

/-! # Candidate coordinate matrix from the actual array solver

Disjoint uncompiled draft. For each physical unit right-hand side, this matrix
reads the free-kernel candidate selected by the actual array-backed span
solver and restricts it to the original coefficient columns. Full column span
proves that the solver does not take its zero default on any such right-hand
side. This draft does not yet prove that these entries solve the systems; the
remaining bridge is a candidate-specific kernel-to-affine-equation theorem.
-/

/-- The actual deterministic free-candidate coefficients returned for one
physical unit right-hand side, with zero used only when the span scan returns
no witness. Rows are array-column coefficients and columns are physical
coordinate right-hand sides. -/
def actualGreedyArrayCandidateInverseMatrix {m : Nat}
    (columns : Array (Fin m → ZMod 2)) :
    Matrix (Fin columns.size) (Fin m) (ZMod 2) :=
  fun coefficientIndex rhsIndex =>
    let target : Fin m → ZMod 2 := Pi.single rhsIndex 1
    let scan := actualGreedyArrayAugmentedScan columns target
    match actualGreedyArraySpanWitness? columns target with
    | none => 0
    | some free =>
        balanceGaussianFreeKernelCandidate
          (actualBalanceGaussianArrayView
            (m := m) (n := columns.size + 1) scan.1)
          scan.2 free coefficientIndex.castSucc

/-- Every physical unit right-hand side has an actual returned free-index
witness when the array columns span the physical space. -/
theorem actualGreedyArraySpanWitness?_some_of_top {m : Nat}
    (columns : Array (Fin m → ZMod 2))
    (hspan : actualGreedyArrayColumnSubmodule columns = ⊤)
    (rhsIndex : Fin m) :
    ∃ free, actualGreedyArraySpanWitness? columns
      (Pi.single rhsIndex 1) = some free := by
  apply actualGreedyArraySpanWitness?_complete
  apply (actualGreedyArrayColumnSpanContains_iff_mem_span columns _).2
  have hmem : (Pi.single rhsIndex 1 : Fin m → ZMod 2) ∈
      actualGreedyArrayColumnSubmodule columns := by
    rw [hspan]
    exact Submodule.mem_top
  exact hmem

/-- Under full span, no entry of the candidate inverse uses the zero-default
branch: each column is produced by the actual finite free-candidate search. -/
theorem actualGreedyArrayCandidateInverseMatrix_no_default_of_top {m : Nat}
    (columns : Array (Fin m → ZMod 2))
    (hspan : actualGreedyArrayColumnSubmodule columns = ⊤) :
    ∀ rhsIndex, ∃ free,
      actualGreedyArraySpanWitness? columns (Pi.single rhsIndex 1) = some free := by
  intro rhsIndex
  exact actualGreedyArraySpanWitness?_some_of_top columns hspan rhsIndex

/-- The actual three-pass output has an executable candidate-inverse matrix
whose selector returns a real free candidate for every physical unit. This
connects the solver output to the run, while leaving candidate-specific
equation correctness for the next bridge. -/
theorem actualGreedyArrayOrbitRun_threePass_candidateInverse
    {s : Nat} (hs : 1 ≤ s)
    (T : Module.End (ZMod 2) (BinaryVector (3 * s)))
    (p : Polynomial (ZMod 2)) (hp : Irreducible p) (hmonic : p.Monic)
    (hdeg : p.natDegree = s) (hroot : Polynomial.aeval T p = 0) :
    ∃ outColumns outSelected,
      actualGreedyArrayOrbitRun T 3
        (#[] : Array (BinaryVector (3 * s))) #[] =
          some (outColumns, outSelected) ∧
      outColumns.size = 3 * s ∧
      ∀ rhsIndex : Fin (3 * s), ∃ free,
        actualGreedyArraySpanWitness? outColumns
          (Pi.single rhsIndex 1) = some free := by
  obtain ⟨outColumns, outSelected, outSpan, hrun, _, houtColumnsSize,
      houtDim, houtSpan, _⟩ :=
    actualGreedyArrayOrbitRun_threePass hs T p hp hmonic hdeg hroot
  have houtColumnsTop : actualGreedyArrayColumnSubmodule outColumns = ⊤ := by
    rw [houtSpan]
    apply Submodule.eq_top_of_finrank_eq
    simpa [BinaryVector, Module.finrank_pi] using houtDim
  refine ⟨outColumns, outSelected, hrun, houtColumnsSize, ?_⟩
  intro rhsIndex
  exact actualGreedyArraySpanWitness?_some_of_top
    outColumns houtColumnsTop rhsIndex

end CorruptedFieldRecovery
