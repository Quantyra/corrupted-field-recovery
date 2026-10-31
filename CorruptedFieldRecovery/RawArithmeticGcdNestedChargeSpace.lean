import CorruptedFieldRecovery.RawArithmeticGcdNestedStackTrace

/-! Charge-based corollaries for the nested GCD/remainder register-stack
trace. The charge is the accepted recurrence model; these are not processor
runtime or Lean heap estimates. -/

namespace CorruptedFieldRecovery

/-- The nested GCD/remainder stack depth is bounded by the declared GCD charge
times the input-width allowance for one GCD level and its reducer call. -/
theorem rawPolynomialGcdNestedStackTrace_length_le_charge
    {a b W : Nat} (hW : 0 < W) (ha : a < 2 ^ W) (hb : b < 2 ^ W) :
    ∀ stack ∈ rawPolynomialGcdNestedStackTrace a b,
      stack.length ≤ (rawPolynomialGcdBitCosted a b).2 * (W + 2) := by
  intro stack hstack
  have hdepth := rawPolynomialGcdNestedStackTrace_length_le hW ha hb stack hstack
  have hcharge := rawPolynomialGcdBitCostedFrames_le_charge a b
  exact le_trans hdepth (Nat.mul_le_mul_right (W + 2) hcharge)

/-- The nested GCD/remainder stack live-bit measure is bounded directly by
the accepted declared GCD charge and the proved per-frame width envelope. -/
theorem rawPolynomialGcdNestedStackTrace_live_bits_le_charge
    {a b W : Nat} (hW : 0 < W) (ha : a < 2 ^ W) (hb : b < 2 ^ W) :
    ∀ stack ∈ rawPolynomialGcdNestedStackTrace a b,
      rawArithmeticStackLiveBits stack ≤
        ((rawPolynomialGcdBitCosted a b).2 * (W + 2)) *
          (3 + 6 * (rawArithmeticParameterWidth W + 1)) := by
  intro stack hstack
  have hspace := rawPolynomialGcdNestedStackTrace_live_bits_le hW ha hb stack hstack
  have hcharge := rawPolynomialGcdBitCostedFrames_le_charge a b
  have hdepth := Nat.mul_le_mul_right (W + 2) hcharge
  exact le_trans hspace (Nat.mul_le_mul_right
    (3 + 6 * (rawArithmeticParameterWidth W + 1)) hdepth)

end CorruptedFieldRecovery
