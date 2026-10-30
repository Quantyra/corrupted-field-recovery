import CorruptedFieldRecovery.RawRabinRemainderCost
import CorruptedFieldRecovery.RawRabinGcdCorrectness

/-! Cost instrumentation and width descent for the actual Nat-mask Euclidean
GCD used by the fast Rabin check. -/

namespace CorruptedFieldRecovery

open Polynomial

/-- For divisor masks above one, polynomial long division returns a remainder
whose degree is strictly below the divisor degree. -/
theorem rawPolynomialRemainder_lt_pow_log {a b : Nat} (hb : 1 < b) :
    rawPolynomialRemainder a b < 2 ^ Nat.log2 b := by
  have hb0 : b ≠ 0 := by omega
  have hlow : 2 ^ Nat.log2 b ≤ b := Nat.log2_self_le hb0
  have hupp : b < 2 ^ (Nat.log2 b + 1) := Nat.lt_log2_self
  have hs : 0 < Nat.log2 b := by
    by_contra h
    have hz : Nat.log2 b = 0 := by omega
    rw [hz] at hupp
    omega
  have hfuel : Nat.log2 a - Nat.log2 b + 1 ≤ Nat.log2 a + 1 := by omega
  have hred := rawReduceFuel_lt_of_modulus_band_logFuel
    (Nat.log2 b) b a (Nat.log2 a + 1) hlow hupp hs hfuel
  unfold rawPolynomialRemainder
  simp only [if_neg hb0, if_neg (by omega : b ≠ 1)]
  exact hred

/-- Instrumented execution of the exact Euclidean recursion. Each active
level charges its divisor-width branch/control and the paired remainder cost. -/
def rawPolynomialGcdBitCosted : Nat → Nat → Nat × Nat
  | a, 0 => (a, rawNatBitWidth 0)
  | _, 1 => (1, rawNatBitWidth 1)
  | a, b + 2 =>
      let rem := rawPolynomialRemainderBitCosted a (b + 2)
      let rest := rawPolynomialGcdBitCosted (b + 2) rem.1
      (rest.1, rawNatBitWidth (b + 2) + rem.2 + rest.2)
termination_by _ b => b
decreasing_by
  rw [rawPolynomialRemainderBitCosted_fst]
  exact rawPolynomialRemainder_lt (by omega)

/-- The costed Euclidean recursion returns exactly `rawPolynomialGcd`. -/
theorem rawPolynomialGcdBitCosted_fst (a b : Nat) :
    (rawPolynomialGcdBitCosted a b).1 = rawPolynomialGcd a b := by
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
      cases b with
      | zero => simp [rawPolynomialGcdBitCosted, rawPolynomialGcd]
      | succ b =>
          cases b with
          | zero => simp [rawPolynomialGcdBitCosted, rawPolynomialGcd]
          | succ b =>
              let rem := rawPolynomialRemainderBitCosted a (b + 2)
              have hrem : rem.1 < b + 2 := by
                rw [rawPolynomialRemainderBitCosted_fst]
                exact rawPolynomialRemainder_lt (by omega)
              simp only [rawPolynomialGcdBitCosted, rawPolynomialGcd]
              rw [ih rem.1 hrem]
              rw [rawPolynomialRemainderBitCosted_fst]

end CorruptedFieldRecovery
