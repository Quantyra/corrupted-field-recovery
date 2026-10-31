import CorruptedFieldRecovery.S010BalanceGaussianArrayCandidateInverse
import CorruptedFieldRecovery.S010BalanceGaussianArrayCandidateSolutionFixed2
import Mathlib.LinearAlgebra.Matrix.ToLin

open scoped Matrix

namespace CorruptedFieldRecovery

/-! # Product identities for the actual array candidate inverse

Disjoint uncompiled proof. This composes the selected-candidate affine-fit
lemma with the returned candidate matrix. It proves both rectangular product
identities under exact array length and full span. The three-pass corollary
shows these hypotheses follow from the executable run. Raw square-matrix
reindexing and serialization remain separate follow-up work.
-/

/-- The matrix made from the actual selected free-kernel candidates is a
right inverse of the array column matrix when the latter has full span. -/
theorem actualGreedyArrayCandidateInverseMatrix_two_sided_of_top
    {m : Nat} (columns : Array (BinaryVector m))
    (hsize : columns.size = m)
    (hspan : actualGreedyArrayColumnSubmodule columns = ⊤) :
    actualGreedyArraySpanMatrix columns *
        actualGreedyArrayCandidateInverseMatrix columns = 1 ∧
      actualGreedyArrayCandidateInverseMatrix columns *
        actualGreedyArraySpanMatrix columns = 1 := by
  let A := actualGreedyArraySpanMatrix columns
  let B := actualGreedyArrayCandidateInverseMatrix columns
  have hfamily : A.col = actualGreedyArrayColumnFamily columns := by
    funext j i
    rfl
  have hspanA : Submodule.span (ZMod 2) (Set.range A.col) = ⊤ := by
    rw [hfamily, ← actualGreedyArrayColumnSubmodule_eq_span]
    exact hspan
  have hli : LinearIndependent (ZMod 2) A.col :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspanA.ge (by
      simp [hsize])
  have hinj : Function.Injective (A *ᵥ ·) :=
    Matrix.mulVec_injective_iff.mpr hli
  have hleft : A * B = 1 := by
    ext row rhsIndex
    obtain ⟨free, hfound⟩ :=
      actualGreedyArraySpanWitness?_some_of_top columns hspan rhsIndex
    let target : Fin m → ZMod 2 := Pi.single rhsIndex 1
    let run := actualGreedyArrayAugmentedScan columns target
    let candidate := balanceGaussianFreeKernelCandidate
      (actualBalanceGaussianArrayView
        (m := m) (n := columns.size + 1) run.1) run.2 free
    have hsolve : A *ᵥ (fun i => candidate i.castSucc) = target := by
      simpa [A, target, run, candidate] using
        actualGreedyArraySpanWitness?_selectedCandidate_solves
          columns target hfound
    have hcol : B.col rhsIndex = (fun i => candidate i.castSucc) := by
      funext i
      simp [B, actualGreedyArrayCandidateInverseMatrix, target, run,
        candidate, hfound]
    calc
      (A * B) row rhsIndex = (A *ᵥ B.col rhsIndex) row := by
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
      _ = target row := by rw [hcol]; exact congrFun hsolve row
      _ = (1 : Matrix (Fin m) (Fin m) (ZMod 2)) row rhsIndex := by
        rw [Matrix.one_apply]
        by_cases hrow : row = rhsIndex
        · subst hrow
          simp [target]
        · simp [target, hrow]
  have hBA : ∀ x : Fin columns.size → ZMod 2,
      B *ᵥ (A *ᵥ x) = x := by
    intro x
    apply hinj
    calc
      A *ᵥ (B *ᵥ (A *ᵥ x)) = (A * B) *ᵥ (A *ᵥ x) := by
        rw [← Matrix.mulVec_mulVec]
      _ = (1 : Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ (A *ᵥ x) := by
        rw [hleft]
      _ = A *ᵥ x := by simp
  have hright : B * A = 1 := by
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [← Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
  exact ⟨hleft, hright⟩

/-- The actual three-pass run returns an array whose candidate inverse matrix
satisfies both multiplication identities. The hypotheses are the exact
monic irreducible annihilator conditions used by the run. -/
theorem actualGreedyArrayOrbitRun_threePass_candidateInverse_two_sided
    {s : Nat} (hs : 1 ≤ s)
    (T : Module.End (ZMod 2) (BinaryVector (3 * s)))
    (p : Polynomial (ZMod 2)) (hp : Irreducible p) (hmonic : p.Monic)
    (hdeg : p.natDegree = s) (hroot : Polynomial.aeval T p = 0) :
    ∃ outColumns outSelected,
      actualGreedyArrayOrbitRun T 3
        (#[] : Array (BinaryVector (3 * s))) #[] =
          some (outColumns, outSelected) ∧
      outColumns.size = 3 * s ∧
      actualGreedyArraySpanMatrix outColumns *
          actualGreedyArrayCandidateInverseMatrix outColumns = 1 ∧
      actualGreedyArrayCandidateInverseMatrix outColumns *
          actualGreedyArraySpanMatrix outColumns = 1 := by
  obtain ⟨outColumns, outSelected, outSpan, hrun, _, houtColumnsSize,
      houtDim, houtSpan, _⟩ :=
    actualGreedyArrayOrbitRun_threePass hs T p hp hmonic hdeg hroot
  have houtColumnsTop : actualGreedyArrayColumnSubmodule outColumns = ⊤ := by
    rw [houtSpan]
    apply Submodule.eq_top_of_finrank_eq
    simpa [BinaryVector, Module.finrank_pi] using houtDim
  obtain ⟨hleft, hright⟩ :=
    actualGreedyArrayCandidateInverseMatrix_two_sided_of_top
      outColumns houtColumnsSize houtColumnsTop
  exact ⟨outColumns, outSelected, hrun, houtColumnsSize, hleft, hright⟩

end CorruptedFieldRecovery
