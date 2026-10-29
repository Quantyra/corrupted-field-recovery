import CorruptedFieldRecovery.RawFieldTraceBits
import CorruptedFieldRecovery.RawFieldQuotient
import Mathlib.FieldTheory.Finite.Trace

/-! Algebraic bridge from the executable Frobenius-sum evaluator to the
library field trace. -/

namespace CorruptedFieldRecovery

open AdjoinRoot

/-- The candidate quotient has degree `s` over its prime field. -/
theorem accepted_rawCandidate_finrank {s : Nat}
    (candidate : RawFieldCandidate s)
    (hcheck : rawFieldCandidateCheck candidate = true) :
    Module.finrank (ZMod 2) (AdjoinRoot (rawCandidateModulus candidate)) = s := by
  have hvalid := accepted_rawFieldCandidateCheck candidate hcheck
  have hmod := rawFieldCandidateValid_modulus_polynomial candidate hvalid
  letI : Fact (Irreducible (rawCandidateModulus candidate)) :=
    ⟨accepted_rawCandidateModulus_irreducible candidate hcheck⟩
  rw [Module.finrank_eq_card_basis
    (AdjoinRoot.powerBasisAux' (by simpa [rawCandidateModulus] using hmod.1))]
  simp [rawCandidateModulus, hmod.2]

/-- The executable trace mask represents the algebra trace of the decoded
input in the accepted quotient field. -/
theorem rawFieldTraceBits_quotient_eq_algebraTrace {s : Nat}
    (candidate : RawFieldCandidate s)
    (hcheck : rawFieldCandidateCheck candidate = true) (x : Nat) :
    rawCandidateQuotientClass candidate (rawFieldTraceBits candidate hcheck x) =
      Algebra.trace (ZMod 2) (AdjoinRoot (rawCandidateModulus candidate))
        (rawCandidateQuotientClass candidate x) := by
  have hvalid := accepted_rawFieldCandidateCheck candidate hcheck
  have hmod := rawFieldCandidateValid_modulus_polynomial candidate hvalid
  letI : Fact (Irreducible (rawCandidateModulus candidate)) :=
    ⟨accepted_rawCandidateModulus_irreducible candidate hcheck⟩
  let K := AdjoinRoot (rawCandidateModulus candidate)
  letI : Module.Finite (ZMod 2) K := by
    simpa [rawCandidateModulus] using hmod.1.finite_adjoinRoot
  letI : Finite K := Module.finite_of_finite (ZMod 2)
  have hsum := rawFieldTraceAux_quotient_eq_frobenius_sum candidate hcheck
    s x 0
  have heval :
      rawCandidateQuotientClass candidate (rawFieldTraceBits candidate hcheck x) =
        ∑ i ∈ Finset.range s,
          (rawCandidateQuotientClass candidate x) ^ (2 ^ i) := by
    simpa [rawFieldTraceBits, rawFieldTraceAux, rawCandidateQuotientClass,
      rawMaskPolynomial_zero] using hsum
  have htrace := FiniteField.algebraMap_trace_eq_sum_pow
    (ZMod 2) K (rawCandidateQuotientClass candidate x)
  have htrace' :
      algebraMap (ZMod 2) K
        (Algebra.trace (ZMod 2) K (rawCandidateQuotientClass candidate x)) =
        ∑ i ∈ Finset.range s,
          (rawCandidateQuotientClass candidate x) ^ (2 ^ i) := by
    simpa [K, accepted_rawCandidate_finrank candidate hcheck,
      Nat.card_eq_fintype_card, ZMod.card] using htrace
  exact heval.trans htrace'.symm

end CorruptedFieldRecovery
