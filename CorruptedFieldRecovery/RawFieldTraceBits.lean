import CorruptedFieldRecovery.RawReductionLogFuel
import Mathlib.FieldTheory.Finite.Trace

/-! Executable bit-mask trace arithmetic for the accepted quotient-field
candidate. The evaluator uses repeated squaring and XOR accumulation; its
semantic bridge identifies the output with the Frobenius trace sum. -/

namespace CorruptedFieldRecovery

/-- The quotient class denoted by a raw polynomial mask. -/
noncomputable def rawCandidateQuotientClass {s : Nat} (candidate : RawFieldCandidate s)
    (a : Nat) : AdjoinRoot (rawCandidateModulus candidate) :=
  AdjoinRoot.mk (rawCandidateModulus candidate) (rawMaskPolynomial a)

/-- Executable multiplication of two raw masks in the candidate quotient. -/
def rawFieldMulBits {s : Nat} (candidate : RawFieldCandidate s)
    (hcheck : rawFieldCandidateCheck candidate = true) (a b : Nat) : Nat :=
  let _ := hcheck
  rawFieldMulFuel candidate (Nat.log2 (rawPolyMul a b) - s + 1) a b

theorem rawFieldMulBits_quotient_sound {s : Nat}
    (candidate : RawFieldCandidate s)
    (hcheck : rawFieldCandidateCheck candidate = true) (a b : Nat) :
    rawCandidateQuotientClass candidate (rawFieldMulBits candidate hcheck a b) =
      rawCandidateQuotientClass candidate a * rawCandidateQuotientClass candidate b := by
  simpa [rawCandidateQuotientClass, rawFieldMulBits] using
    rawFieldMulFuel_quotient_sound candidate
      (Nat.log2 (rawPolyMul a b) - s + 1) a b

/-- XOR of raw masks represents addition in the polynomial quotient. -/
theorem rawFieldAddBits_quotient_sound {s : Nat}
    (candidate : RawFieldCandidate s) (a b : Nat) :
    rawCandidateQuotientClass candidate (Nat.xor a b) =
      rawCandidateQuotientClass candidate a + rawCandidateQuotientClass candidate b := by
  change AdjoinRoot.mk (rawCandidateModulus candidate)
      (rawMaskPolynomial (Nat.xor a b)) =
    AdjoinRoot.mk (rawCandidateModulus candidate) (rawMaskPolynomial a) +
      AdjoinRoot.mk (rawCandidateModulus candidate) (rawMaskPolynomial b)
  rw [rawMaskPolynomial_xor]
  exact map_add (AdjoinRoot.mk (rawCandidateModulus candidate)) _ _

/-- Repeated squaring and XOR accumulation for the prime-field trace sum. -/
def rawFieldTraceAux {s : Nat} (candidate : RawFieldCandidate s)
    (hcheck : rawFieldCandidateCheck candidate = true) : Nat → Nat → Nat → Nat
  | 0, _current, accumulator => accumulator
  | n + 1, current, accumulator =>
      rawFieldTraceAux candidate hcheck n
        (rawFieldMulBits candidate hcheck current current)
        (Nat.xor current accumulator)

/-- The serialized trace mask, using exactly `s` Frobenius terms. -/
def rawFieldTraceBits {s : Nat} (candidate : RawFieldCandidate s)
    (hcheck : rawFieldCandidateCheck candidate = true) (x : Nat) : Nat :=
  rawFieldTraceAux candidate hcheck s x 0

/-- The trace evaluator's quotient class is the sum of the `s` successive
Frobenius powers of the input class. -/
theorem rawFieldTraceAux_quotient_eq_frobenius_sum {s : Nat}
    (candidate : RawFieldCandidate s)
    (hcheck : rawFieldCandidateCheck candidate = true) :
    ∀ (n x accumulator : Nat),
      rawCandidateQuotientClass candidate
          (rawFieldTraceAux candidate hcheck n x accumulator) =
        rawCandidateQuotientClass candidate accumulator +
          ∑ i ∈ Finset.range n,
            (rawCandidateQuotientClass candidate x) ^ (2 ^ i) := by
  intro n
  induction n with
  | zero =>
      intro x accumulator
      simp [rawFieldTraceAux]
  | succ n ih =>
      intro x accumulator
      calc
        rawCandidateQuotientClass candidate
            (rawFieldTraceAux candidate hcheck (n + 1) x accumulator) =
          rawCandidateQuotientClass candidate
            (rawFieldTraceAux candidate hcheck n
              (rawFieldMulBits candidate hcheck x x) (Nat.xor x accumulator)) := rfl
        _ = rawCandidateQuotientClass candidate (Nat.xor x accumulator) +
              ∑ i ∈ Finset.range n,
                (rawCandidateQuotientClass candidate
                  (rawFieldMulBits candidate hcheck x x)) ^ (2 ^ i) := ih _ _
        _ = (rawCandidateQuotientClass candidate x +
              rawCandidateQuotientClass candidate accumulator) +
              ∑ i ∈ Finset.range n,
                ((rawCandidateQuotientClass candidate x) ^ 2) ^ (2 ^ i) := by
              rw [rawFieldAddBits_quotient_sound, rawFieldMulBits_quotient_sound]
              simp only [pow_two]
        _ = rawCandidateQuotientClass candidate accumulator +
              ∑ i ∈ Finset.range (n + 1),
                (rawCandidateQuotientClass candidate x) ^ (2 ^ i) := by
              have hsum :
                  ∑ i ∈ Finset.range n,
                    ((rawCandidateQuotientClass candidate x) ^ 2) ^ (2 ^ i) =
                  ∑ i ∈ Finset.range n,
                    (rawCandidateQuotientClass candidate x) ^ (2 ^ (i + 1)) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [← pow_mul]
                congr 1
                rw [pow_succ]
                ring
              rw [hsum, Finset.sum_range_succ']
              simp only [pow_zero, pow_one]
              ac_rfl

/-- For an accepted degree-`s` field candidate and an `s`-bit input, the
trace routine returns an `s`-bit mask. -/
theorem rawFieldTraceBits_lt_pow {s : Nat}
    (candidate : RawFieldCandidate s)
    (hcheck : rawFieldCandidateCheck candidate = true)
    (x : Nat) (hx : x < 2 ^ s) :
    rawFieldTraceBits candidate hcheck x < 2 ^ s := by
  have hs : 0 < s := by
    have hv := accepted_rawFieldCandidateCheck candidate hcheck
    rcases hv with ⟨hs, hmod, htop, hscalarSize, hscalar, hirred⟩
    omega
  have hmul_lt : ∀ a b, rawFieldMulBits candidate hcheck a b < 2 ^ s := by
    intro a b
    simpa [rawFieldMulBits] using
      rawFieldMulFuel_lt_of_accepted candidate hcheck a b
  have haux : ∀ n current accumulator,
      current < 2 ^ s → accumulator < 2 ^ s →
      rawFieldTraceAux candidate hcheck n current accumulator < 2 ^ s := by
    intro n
    induction n with
    | zero =>
        intro current accumulator hcurrent hacc
        simpa [rawFieldTraceAux] using hacc
    | succ n ih =>
        intro current accumulator hcurrent hacc
        have hnewCurrent := hmul_lt current current
        have hnewAccumulator : Nat.xor current accumulator < 2 ^ s := by
          apply Nat.bitwise_lt_two_pow
          · exact hcurrent
          · exact hacc
        exact ih _ _ hnewCurrent hnewAccumulator
  have hzero : 0 < 2 ^ s := by positivity
  exact haux s x 0 hx (by omega)

end CorruptedFieldRecovery
