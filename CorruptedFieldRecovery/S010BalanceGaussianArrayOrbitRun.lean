import CorruptedFieldRecovery.S010BalanceGaussianArrayOrbitAppend

namespace CorruptedFieldRecovery

/-! # Three actual array passes

This source is deliberately separate from the accepted one-step results.  The
run below executes the first-outside-unit selector and appends the computed
orbit array.  The summary theorem derives selector success from properness at
each pass; it does not take selected units as input.  It remains dependent on
the append refinement and quotient-orbit theorem being accepted and compiled.
-/

/-- One recursive pass of the actual array-driven physical-unit/orbit scan.
The selected units are recorded in order for subsequent constructor stages. -/
def actualGreedyArrayOrbitRun {s : Nat}
    (T : Module.End (ZMod 2) (BinaryVector (3 * s))) :
    Nat → Array (BinaryVector (3 * s)) → Array (Fin (3 * s)) →
      Option (Array (BinaryVector (3 * s)) × Array (Fin (3 * s)))
  | 0, columns, selected => some (columns, selected)
  | k + 1, columns, selected =>
      match actualGreedyArrayFirstUnitOutside? columns with
      | none => none
      | some i =>
          actualGreedyArrayOrbitRun T k
            (columns ++ actualGreedyArrayOrbitColumns (s := s) T
              (actualGreedyArrayUnitVector i))
            (selected.push i)

/-- The recursive run's semantic invariant after `k` successful passes. -/
def ActualGreedyArrayOrbitRunSummary {s k : Nat}
    (T : Module.End (ZMod 2) (BinaryVector (3 * s)))
    (columns : Array (BinaryVector (3 * s)))
    (selected : Array (Fin (3 * s)))
    (M : Submodule (ZMod 2) (BinaryVector (3 * s))) (d : Nat) : Prop :=
  ∃ outColumns outSelected outSpan,
    actualGreedyArrayOrbitRun T k columns selected =
      some (outColumns, outSelected) ∧
    actualGreedyArrayColumnSubmodule outColumns = outSpan ∧
    Module.finrank (ZMod 2) outSpan = d + k * s ∧
    (∀ x, x ∈ outSpan → T x ∈ outSpan) ∧
    M ≤ outSpan ∧
    outSelected.size = selected.size + k ∧
    outColumns.size = columns.size + k * s

/-- Every requested pass succeeds while the remaining orbit blocks fit below
the ambient dimension.  Properness supplies an outside physical unit; the
concrete selector is proved to find one, and the accepted one-step orbit
result proves exact dimension growth and invariance. -/
theorem actualGreedyArrayOrbitRun_summary
    {s k d : Nat} (T : Module.End (ZMod 2) (BinaryVector (3 * s)))
    (columns : Array (BinaryVector (3 * s)))
    (selected : Array (Fin (3 * s)))
    (M : Submodule (ZMod 2) (BinaryVector (3 * s)))
    (hs : 1 ≤ s)
    (p : Polynomial (ZMod 2)) (hp : Irreducible p) (hmonic : p.Monic)
    (hdeg : p.natDegree = s) (hroot : Polynomial.aeval T p = 0)
    (hspan : actualGreedyArrayColumnSubmodule columns = M)
    (hdim : Module.finrank (ZMod 2) M = d)
    (hT : ∀ x, x ∈ M → T x ∈ M)
    (hbudget : d + k * s ≤ 3 * s) :
    ActualGreedyArrayOrbitRunSummary (k := k) T columns selected M d := by
  induction k generalizing columns selected M d hspan hdim hT with
  | zero =>
      refine ⟨columns, selected, M, ?_, hspan, ?_, hT, le_rfl, ?_, ?_⟩
      · simp [actualGreedyArrayOrbitRun]
      · simpa using hdim
      · simp
      · simp
  | succ k ih =>
      have hbudget' : d + (k * s + s) ≤ 3 * s := by
        simpa [Nat.succ_mul] using hbudget
      have hlt : d < 3 * s := by omega
      have hproper : M ≠ ⊤ := by
        intro htop
        have htopdim : Module.finrank (ZMod 2)
            (⊤ : Submodule (ZMod 2) (BinaryVector (3 * s))) = 3 * s := by
          rw [finrank_top, Module.finrank_eq_card_basis
            (Pi.basisFun (ZMod 2) (Fin (3 * s)))]
          simp
        rw [htop, htopdim] at hdim
        omega
      have hTcols : ∀ x, x ∈ actualGreedyArrayColumnSubmodule columns →
          T x ∈ actualGreedyArrayColumnSubmodule columns := by
        intro x hx
        rw [hspan] at hx ⊢
        exact hT x hx
      obtain ⟨i, hfind, houtside, hgrowth, hnextT⟩ :=
        actualGreedyArraySelectedOrbit_step T columns p hs hdeg hp hmonic
          hroot hTcols (by simpa [hspan] using hproper)
      let nextColumns := columns ++ actualGreedyArrayOrbitColumns (s := s) T
        (actualGreedyArrayUnitVector i)
      let nextSelected := selected.push i
      let nextM : Submodule (ZMod 2) (BinaryVector (3 * s)) :=
        M ⊔ actualGreedyOrbitSpan (s := s) T (actualGreedyArrayUnitVector i)
      have hnextSpan : actualGreedyArrayColumnSubmodule nextColumns = nextM := by
        change actualGreedyArrayColumnSubmodule
          (columns ++ actualGreedyArrayOrbitColumns (s := s) T
            (actualGreedyArrayUnitVector i)) =
          M ⊔ actualGreedyOrbitSpan (s := s) T (actualGreedyArrayUnitVector i)
        rw [actualGreedyArrayAppendOrbit_span, hspan]
      have hnextDim : Module.finrank (ZMod 2) nextM = d + s := by
        have hgrowth' : Module.finrank (ZMod 2)
            (show Submodule (ZMod 2) (BinaryVector (3 * s)) from
              M ⊔ actualGreedyOrbitSpan (s := s) T
                (actualGreedyArrayUnitVector i)) = d + s := by
          calc
            Module.finrank (ZMod 2)
                (show Submodule (ZMod 2) (BinaryVector (3 * s)) from
                  M ⊔ actualGreedyOrbitSpan (s := s) T
                    (actualGreedyArrayUnitVector i)) =
              Module.finrank (ZMod 2)
                (show Submodule (ZMod 2) (BinaryVector (3 * s)) from
                  actualGreedyArrayColumnSubmodule columns ⊔
                    actualGreedyOrbitSpan (s := s) T
                      (actualGreedyArrayUnitVector i)) := by rw [hspan]
            _ = Module.finrank (ZMod 2)
                  (actualGreedyArrayColumnSubmodule columns) + s := hgrowth
            _ = d + s := by rw [hspan, hdim]
        simpa [nextM, hspan] using hgrowth'
      have hnextTM : ∀ x, x ∈ nextM → T x ∈ nextM := by
        simpa [nextM, hspan] using hnextT
      have hnextBudget : (d + s) + k * s ≤ 3 * s := by
        omega
      obtain ⟨outColumns, outSelected, outSpan, hrun, houtSpan, houtDim,
        houtT, hnextLe, houtSelectedSize, houtColumnsSize⟩ :=
          ih (columns := nextColumns) (selected := nextSelected) (M := nextM)
            (d := d + s) hnextSpan hnextDim hnextTM hnextBudget
      refine ⟨outColumns, outSelected, outSpan, ?_, houtSpan, ?_, houtT,
        ?_, ?_, ?_⟩
      · simp [actualGreedyArrayOrbitRun, hfind, nextColumns, nextSelected, hrun]
      · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
          Nat.succ_mul, Nat.mul_add, add_mul] using houtDim
      · exact le_trans le_sup_left hnextLe
      · simpa [nextSelected, Array.size_push, Nat.add_assoc,
          Nat.add_left_comm, Nat.add_comm] using houtSelectedSize
      · simpa [nextColumns, Array.size_append, actualGreedyArrayOrbitColumns,
          Array.size_ofFn, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
          Nat.succ_mul, Nat.mul_add, add_mul] using houtColumnsSize

/-- Three successful actual passes produce three selected physical units and
exactly `3s` orbit columns whose span has full dimension and is T-invariant.
The hypotheses are the explicit good-reference-tape algebraic premises used
by the one-step theorem: a monic irreducible degree-`s` annihilator for `T`. -/
theorem actualGreedyArrayOrbitRun_threePass
    {s : Nat} (hs : 1 ≤ s)
    (T : Module.End (ZMod 2) (BinaryVector (3 * s)))
    (p : Polynomial (ZMod 2)) (hp : Irreducible p) (hmonic : p.Monic)
    (hdeg : p.natDegree = s) (hroot : Polynomial.aeval T p = 0) :
      ∃ outColumns outSelected,
        ∃ (outSpan : Submodule (ZMod 2) (BinaryVector (3 * s))),
      actualGreedyArrayOrbitRun T 3 (#[] : Array (BinaryVector (3 * s))) #[] =
        some (outColumns, outSelected) ∧
      outSelected.size = 3 ∧ outColumns.size = 3 * s ∧
      Module.finrank (ZMod 2) outSpan = 3 * s ∧
      actualGreedyArrayColumnSubmodule outColumns = outSpan ∧
      (∀ x, x ∈ outSpan → T x ∈ outSpan) := by
  have hinit : actualGreedyArrayColumnSubmodule
      (#[] : Array (BinaryVector (3 * s))) = ⊥ := by
    rw [actualGreedyArrayColumnSubmodule_eq_span]
    simp [actualGreedyArrayColumnFamily]
  have hbottom : Module.finrank (ZMod 2)
      (⊥ : Submodule (ZMod 2) (BinaryVector (3 * s))) = 0 := by simp
  have hbottomT : ∀ x, x ∈ (⊥ : Submodule (ZMod 2)
      (BinaryVector (3 * s))) → T x ∈
        (⊥ : Submodule (ZMod 2) (BinaryVector (3 * s))) := by
    simp
  obtain ⟨outColumns, outSelected, outSpan, hrun, houtSpan, houtDim,
    houtT, _, houtSelectedSize, houtColumnsSize⟩ :=
      actualGreedyArrayOrbitRun_summary (k := 3) (d := 0) T
        (#[] : Array (BinaryVector (3 * s))) #[] ⊥ hs p hp hmonic hdeg hroot
        hinit hbottom hbottomT (by omega)
  refine ⟨outColumns, outSelected, outSpan, hrun, ?_, ?_, ?_,
    houtSpan, houtT⟩
  · simpa using houtSelectedSize
  · simpa using houtColumnsSize
  · simpa [Nat.zero_add] using houtDim

end CorruptedFieldRecovery
