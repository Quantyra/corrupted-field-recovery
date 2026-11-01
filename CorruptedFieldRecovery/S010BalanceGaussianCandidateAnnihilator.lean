import CorruptedFieldRecovery.RawFieldQuotient
import CorruptedFieldRecovery.RawRabinCandidateCorrectness

/-! The polynomial half of the annihilator premise, derived from the actual
raw candidate rather than assumed.

A finite `RawFieldCandidate s` carries the serialized modulus. The executable
fast check validates the concrete divisor enumeration; this file turns that
single executable acceptance into the algebraic bundle the kernel/annihilator
theorems consume: the candidate modulus is a monic irreducible polynomial of
degree `s`.

The remaining half of the premise, that the model operator is annihilated by
this polynomial, is a statement about the model recurrence and is not derivable
from the candidate array alone; it stays an explicit model hypothesis. -/

namespace CorruptedFieldRecovery

/-- Executable fast-check acceptance yields the algebraic annihilator
bundle: irreducible, monic and of degree `s`. -/
theorem accepted_rawCandidateModulus_annihilator {s : Nat}
    (candidate : RawFieldCandidate s)
    (hfast : rawFieldCandidateFastCheck candidate = true) :
    Irreducible (rawCandidateModulus candidate) ∧
      (rawCandidateModulus candidate).Monic ∧
      (rawCandidateModulus candidate).natDegree = s := by
  have hvalid :=
    (rawFieldCandidateFastCheck_eq_true_iff_valid candidate).mp hfast
  have hcheck : rawFieldCandidateCheck candidate = true := by
    simp [rawFieldCandidateCheck, hvalid]
  refine ⟨accepted_rawCandidateModulus_irreducible candidate hcheck,
    accepted_rawCandidateModulus_monic candidate hcheck, ?_⟩
  exact (rawFieldCandidateValid_modulus_polynomial candidate hvalid).2

end CorruptedFieldRecovery
