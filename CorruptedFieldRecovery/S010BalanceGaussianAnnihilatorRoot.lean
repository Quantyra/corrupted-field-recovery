import CorruptedFieldRecovery.S010BalanceGaussianCandidateAnnihilator

/-! The complete annihilator device for the actual raw candidate.

`S010BalanceGaussianCandidateAnnihilator` derives the polynomial half from the
executable candidate check. This file adds the root half: once the model
supplies the operator `T`, the polynomial `q` produced by the recurrence, and
the two facts that (a) the candidate's serialized modulus is exactly `q` and
(b) `q` annihilates `T`, the candidate modulus annihilates `T` as well.

The two model facts stay explicit hypotheses: neither is a property of the
candidate array, so neither can be derived from it. Everything else is
derived. -/

namespace CorruptedFieldRecovery

/-- The full annihilator device: one executable candidate acceptance plus the
two model-recurrence facts yield a monic irreducible degree-`s` modulus that
annihilates the model operator. -/
theorem accepted_rawCandidateModulus_annihilator_aeval
    {s : Nat} {M : Type*} [AddCommMonoid M] [Module (ZMod 2) M]
    (candidate : RawFieldCandidate s)
    (hfast : rawFieldCandidateFastCheck candidate = true)
    (T : Module.End (ZMod 2) M) (q : Polynomial (ZMod 2))
    (hmod : rawCandidateModulus candidate = q)
    (hq : Polynomial.aeval T q = 0) :
    Irreducible (rawCandidateModulus candidate) ∧
      (rawCandidateModulus candidate).Monic ∧
      (rawCandidateModulus candidate).natDegree = s ∧
      Polynomial.aeval T (rawCandidateModulus candidate) = 0 := by
  obtain ⟨hirr, hmonic, hdeg⟩ :=
    accepted_rawCandidateModulus_annihilator candidate hfast
  refine ⟨hirr, hmonic, hdeg, ?_⟩
  rw [hmod]
  exact hq

/-- Root-only form, for callers that already hold the algebraic bundle. -/
theorem accepted_rawCandidateModulus_aeval_eq_zero
    {s : Nat} {M : Type*} [AddCommMonoid M] [Module (ZMod 2) M]
    (T : Module.End (ZMod 2) M) (candidate : RawFieldCandidate s)
    (q : Polynomial (ZMod 2))
    (hmod : rawCandidateModulus candidate = q)
    (hq : Polynomial.aeval T q = 0) :
    Polynomial.aeval T (rawCandidateModulus candidate) = 0 := by
  rw [hmod]
  exact hq

end CorruptedFieldRecovery
