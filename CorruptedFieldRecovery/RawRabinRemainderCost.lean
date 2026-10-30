import CorruptedFieldRecovery.RawReductionBitCostBounds
import CorruptedFieldRecovery.RawRabinIrreducibility

/-! Instrument the actual divisor-mask remainder used by the Euclidean and
Frobenius loops. The normal branch delegates to the paired `rawReduceFuel`
semantics; zero and unit divisor branches mirror the executable definition. -/

namespace CorruptedFieldRecovery

def rawPolynomialRemainderBitCosted (dividend divisor : Nat) : Nat × Nat :=
  if divisor = 0 then (dividend, rawNatBitWidth divisor + 1)
  else if divisor = 1 then (0, rawNatBitWidth divisor + 1)
  else rawReduceFuelBitCosted divisor (Nat.log2 divisor)
    (Nat.log2 dividend + 1) dividend

theorem rawPolynomialRemainderBitCosted_fst (dividend divisor : Nat) :
    (rawPolynomialRemainderBitCosted dividend divisor).1 =
      rawPolynomialRemainder dividend divisor := by
  by_cases hzero : divisor = 0
  · simp [rawPolynomialRemainderBitCosted, rawPolynomialRemainder, hzero]
  · by_cases hone : divisor = 1
    · simp [rawPolynomialRemainderBitCosted, rawPolynomialRemainder, hone]
    · simp [rawPolynomialRemainderBitCosted, rawPolynomialRemainder,
        hzero, hone, rawReduceFuelBitCosted_fst]

/-- For an `A`-bit dividend and a divisor above one, the actual remainder
routine's declared cost is at most `A` fuel units times the accepted
quadratic-in-width reducer bound. -/
theorem rawPolynomialRemainderBitCosted_cost_le {A dividend divisor : Nat}
    (hA : 0 < A) (hdividend : dividend < 2 ^ A) (hdivisor : 1 < divisor) :
    (rawPolynomialRemainderBitCosted dividend divisor).2 ≤
      A * (40 * (A + Nat.log2 divisor +
        rawNatBitWidth (Nat.log2 divisor) + 4) ^ 2) := by
  have hdivisor0 : divisor ≠ 0 := by omega
  have hmodLower : 2 ^ Nat.log2 divisor ≤ divisor := Nat.log2_self_le hdivisor0
  have hmodUpper : divisor < 2 ^ (Nat.log2 divisor + 1) := Nat.lt_log2_self
  have hdividendLog : Nat.log2 dividend < A :=
    rawLog2_lt_of_lt_pow hA hdividend
  have hfuel : Nat.log2 dividend + 1 ≤ A := by omega
  have hbound := rawReduceFuelBitCosted_cost_le_of_modulus_band
    (Nat.log2 divisor) divisor A (Nat.log2 dividend + 1) dividend
    hmodLower hmodUpper hA hdividend
  have hmul := Nat.mul_le_mul_right
    (40 * (A + Nat.log2 divisor + rawNatBitWidth (Nat.log2 divisor) + 4) ^ 2)
    hfuel
  have hdivisorOne : divisor ≠ 1 := by omega
  have hresult : (rawPolynomialRemainderBitCosted dividend divisor).2 =
      (rawReduceFuelBitCosted divisor (Nat.log2 divisor)
        (Nat.log2 dividend + 1) dividend).2 := by
    simp [rawPolynomialRemainderBitCosted, hdivisor0, hdivisorOne]
  rw [hresult]
  exact le_trans hbound hmul

end CorruptedFieldRecovery
