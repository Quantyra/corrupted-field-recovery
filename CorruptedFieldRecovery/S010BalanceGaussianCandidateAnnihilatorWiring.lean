import CorruptedFieldRecovery.S010BalanceGaussianAnnihilatorRoot
import CorruptedFieldRecovery.S010BalanceGaussianArrayCandidateInverseProofFixed

/-! Wiring the accepted annihilator device into the accepted greedy-orbit run.

The orbit-run theorem takes four supplied algebraic premises (irreducibility,
monicity, degree and the annihilation equation). This file replaces all four
with a single executable candidate acceptance plus the two model-recurrence
facts that the device consumes. -/

namespace CorruptedFieldRecovery

/-- The three-pass greedy orbit run yields a two-sided candidate inverse for
the actual raw candidate: one fast-check acceptance replaces the four supplied
annihilator premises. -/
theorem actualGreedyArrayOrbitRun_threePass_candidateInverse_two_sided_of_candidate
    {s : Nat} (hs : 1 ≤ s)
    (T : Module.End (ZMod 2) (BinaryVector (3 * s)))
    (candidate : RawFieldCandidate s)
    (hfast : rawFieldCandidateFastCheck candidate = true)
    (q : Polynomial (ZMod 2))
    (hmod : rawCandidateModulus candidate = q)
    (hq : Polynomial.aeval T q = 0) :
    ∃ outColumns outSelected,
      actualGreedyArrayOrbitRun T 3
        (#[] : Array (BinaryVector (3 * s))) #[] =
          some (outColumns, outSelected) ∧
      outColumns.size = 3 * s ∧
      actualGreedyArraySpanMatrix outColumns *
          actualGreedyArrayCandidateInverseMatrix outColumns = 1 ∧
      actualGreedyArrayCandidateInverseMatrix outColumns *
          actualGreedyArraySpanMatrix outColumns = 1 := by
  obtain ⟨hirr, hmonic, hdeg, hroot⟩ :=
    accepted_rawCandidateModulus_annihilator_aeval candidate hfast T q hmod hq
  exact actualGreedyArrayOrbitRun_threePass_candidateInverse_two_sided hs T
    (rawCandidateModulus candidate) hirr hmonic hdeg hroot

end CorruptedFieldRecovery
