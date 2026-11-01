import CorruptedFieldRecovery.S010BalanceGaussianCandidateAnnihilatorWiring
import CorruptedFieldRecovery.S010BalanceGaussianSampledGeneratorFilter

/-! Instantiating the accepted wiring against the concrete model recurrence.

`S010BalanceGaussianSampledGeneratorFilter` defines the recurrence polynomial
computed by the manuscript's power-relation solve and records, as an executable
gate hypothesis, that the candidate's serialized modulus equals it. Feeding
that equality and the model's annihilation equation into the accepted wiring
removes the two abstract model facts from the statement. -/

namespace CorruptedFieldRecovery

/-- Three-pass orbit-run candidate inverse, stated directly in terms of the
concrete recurrence polynomial and its annihilation equation. -/
theorem actualGreedyArrayOrbitRun_threePass_candidateInverse_two_sided_of_recurrence
    {s : Nat} (hs : 1 ≤ s)
    (T : Module.End BinaryField (BinaryVector (3 * s)))
    (candidate : RawFieldCandidate s)
    (hfast : rawFieldCandidateFastCheck candidate = true)
    (coefficients : Fin s → BinaryField)
    (henc : rawMaskPolynomial (rawFieldBitsToNat candidate.modulus) =
      actualBalanceGaussianRecurrencePolynomial coefficients)
    (hrecurrence :
      Polynomial.aeval T
        (actualBalanceGaussianRecurrencePolynomial coefficients) = 0) :
    ∃ outColumns outSelected,
      actualGreedyArrayOrbitRun T 3
        (#[] : Array (BinaryVector (3 * s))) #[] =
          some (outColumns, outSelected) ∧
      outColumns.size = 3 * s ∧
      actualGreedyArraySpanMatrix outColumns *
          actualGreedyArrayCandidateInverseMatrix outColumns = 1 ∧
      actualGreedyArrayCandidateInverseMatrix outColumns *
          actualGreedyArraySpanMatrix outColumns = 1 := by
  refine
    actualGreedyArrayOrbitRun_threePass_candidateInverse_two_sided_of_candidate
      hs T candidate hfast
      (actualBalanceGaussianRecurrencePolynomial coefficients) ?_ hrecurrence
  simpa [rawCandidateModulus] using henc

end CorruptedFieldRecovery
