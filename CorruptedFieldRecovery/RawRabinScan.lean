import CorruptedFieldRecovery.RawRabinFactorFrobenius

/-! Exact indexing semantics for the executable bounded Rabin scan. -/

namespace CorruptedFieldRecovery

/-- The `List.range` scan checks exactly the exponents `1 ≤ d ≤ s/2`, with no
off-by-one loss at the degree-one boundary. -/
theorem rawCandidateRabinCheck_eq_true_iff {s : Nat}
    (candidate : RawFieldCandidate s) :
    rawCandidateRabinCheck candidate = true ↔
      ∀ d, 1 ≤ d → d ≤ s / 2 →
        rawPolynomialGcd (rawFieldBitsToNat candidate.modulus)
          (Nat.xor (rawCandidateFrobenius candidate d) 2) = 1 := by
  simp only [rawCandidateRabinCheck, List.all_eq_true, decide_eq_true_eq,
    List.mem_range]
  constructor
  · intro h d hdlo hdhi
    have hindex := h (d - 1) (by omega)
    simpa [Nat.sub_add_cancel (by omega : 1 ≤ d)] using hindex
  · intro h i hi
    have hvalue := h (i + 1) (by omega) (by omega)
    simpa using hvalue

end CorruptedFieldRecovery
