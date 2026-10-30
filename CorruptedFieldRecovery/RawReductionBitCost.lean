import CorruptedFieldRecovery.RawPolynomialBitCost
import CorruptedFieldRecovery.RawReductionLogFuel

/-! Bit-cost semantics for the actual Nat-mask cancellation step and its
fuel-bounded loop. The charge assigns width costs to log/compare/subtract,
power-of-two construction, grade-school multiplication, and XOR. This remains
an abstract algorithmic model, not a Lean machine-runtime claim. -/

namespace CorruptedFieldRecovery

/-- Grade-school bit charge for multiplying two unsigned Nat words. -/
def rawNatMulBitCharge (a b : Nat) : Nat :=
  rawNatBitWidth a * rawNatBitWidth b

/-- Instrument the exact XOR cancellation used by `rawReduceStep`. -/
def rawReduceStepBitCosted (modulus degree a : Nat) : Nat × Nat :=
  let log := Nat.log2 a
  let shift := log - degree
  let power := 2 ^ shift
  let shifted := modulus * power
  let output := Nat.xor a shifted
  (output, 1 + rawNatBitWidth a + rawNatBitWidth degree +
    rawNatBitWidth power + rawNatMulBitCharge modulus power +
    rawNatBitWidth a + rawNatBitWidth shifted)

/-- The cancellation instrument computes exactly the existing raw step. -/
theorem rawReduceStepBitCosted_fst (modulus degree a : Nat) :
    (rawReduceStepBitCosted modulus degree a).1 =
      rawReduceStep modulus degree a := by
  rfl

/-- Fuel-bounded reduction with a paired width-charge accumulator. A zero-fuel
call returns immediately. Every tested level charges the comparison against
`2^degree`; active levels also charge the actual cancellation and recursive
call. -/
def rawReduceFuelBitCosted (modulus degree : Nat) : Nat → Nat → Nat × Nat
  | 0, a => (a, 0)
  | fuel + 1, a =>
      let compareCharge := rawNatBitWidth a + degree + 1
      if a < 2 ^ degree then
        (a, compareCharge)
      else
        let step := rawReduceStepBitCosted modulus degree a
        let rest := rawReduceFuelBitCosted modulus degree fuel step.1
        (rest.1, compareCharge + step.2 + rest.2)

/-- The paired cost semantics refines the exact output of `rawReduceFuel`. -/
theorem rawReduceFuelBitCosted_fst (modulus degree fuel a : Nat) :
    (rawReduceFuelBitCosted modulus degree fuel a).1 =
      rawReduceFuel modulus degree fuel a := by
  induction fuel generalizing a with
  | zero => rfl
  | succ fuel ih =>
      by_cases hsmall : a < 2 ^ degree
      · simp [rawReduceFuelBitCosted, rawReduceFuel, hsmall]
      · simp only [rawReduceFuelBitCosted, rawReduceFuel, if_neg hsmall]
        rw [rawReduceStepBitCosted_fst]
        exact ih _

/-- Exact charge recurrence for the reduction loop. This theorem exposes the
actual stop/step branches to later size proofs without re-running the reducer
or assuming a cost estimate. -/
theorem rawReduceFuelBitCosted_cost_eq (modulus degree : Nat) :
    (∀ fuel a, (rawReduceFuelBitCosted modulus degree fuel a).2 =
      if fuel = 0 then 0 else
        if a < 2 ^ degree then rawNatBitWidth a + degree + 1 else
          rawNatBitWidth a + degree + 1 +
            (rawReduceStepBitCosted modulus degree a).2 +
            (rawReduceFuelBitCosted modulus degree (fuel - 1)
              (rawReduceStepBitCosted modulus degree a).1).2) := by
  intro fuel a
  cases fuel with
  | zero => simp [rawReduceFuelBitCosted]
  | succ fuel =>
      by_cases hsmall : a < 2 ^ degree
      · simp [rawReduceFuelBitCosted, hsmall]
      · simp [rawReduceFuelBitCosted, hsmall]

end CorruptedFieldRecovery
