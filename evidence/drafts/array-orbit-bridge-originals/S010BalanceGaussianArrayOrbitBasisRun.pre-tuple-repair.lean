import CorruptedFieldRecovery.S010BalanceGaussianArrayOrbitBasis

namespace CorruptedFieldRecovery

/-! # Basis witness for the actual three-pass array output

Disjoint uncompiled bridge. It composes the actual recursive run theorem with
full-rank-to-top and the array-family basis construction. The output array is
obtained from the run itself; no basis or successful scan is supplied as an
input. This does not yet construct the square serialized inverse matrix.
-/

/-- Under the explicit monic irreducible annihilator hypotheses, the actual
three-pass output array indexes a basis of physical coordinates. -/
theorem actualGreedyArrayOrbitRun_threePass_basisWitness
    {s : Nat} (hs : 1 ≤ s)
    (T : Module.End (ZMod 2) (BinaryVector (3 * s)))
    (p : Polynomial (ZMod 2)) (hp : Irreducible p) (hmonic : p.Monic)
    (hdeg : p.natDegree = s) (hroot : Polynomial.aeval T p = 0) :
    ∃ outColumns outSelected,
      ∃ (outBasis : Basis (Fin outColumns.size) (ZMod 2)
        (BinaryVector (3 * s))),
      actualGreedyArrayOrbitRun T 3
        (#[] : Array (BinaryVector (3 * s))) #[] =
          some (outColumns, outSelected) ∧
      outColumns.size = 3 * s ∧
      actualGreedyArrayColumnSubmodule outColumns = ⊤ := by
  obtain ⟨outColumns, outSelected, outSpan, hrun, houtSpan, houtDim,
      houtT, _, houtSelectedSize, houtColumnsSize⟩ :=
    actualGreedyArrayOrbitRun_threePass hs T p hp hmonic hdeg hroot
  have houtColumnsTop : actualGreedyArrayColumnSubmodule outColumns = ⊤ := by
    rw [houtSpan]
    apply Submodule.eq_top_of_finrank_eq
    simpa [BinaryVector, finrank_pi] using houtDim
  refine ⟨outColumns, outSelected,
    actualGreedyArrayColumnBasis outColumns houtColumnsSize houtColumnsTop,
    hrun, houtColumnsSize, houtColumnsTop⟩

end CorruptedFieldRecovery
