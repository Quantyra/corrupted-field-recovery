import CorruptedFieldRecovery.RawReductionOperationalMachine
import CorruptedFieldRecovery.RawRabinGcdBitCostBounds

/-! A high-level Euclidean GCD machine whose active transition contains an
execution witness for its actual bounded-reduction subcall. Charges remain
the declared recurrence costs; this is not compiled-machine or Lean-runtime
semantics. -/

namespace CorruptedFieldRecovery

/-- Control state for the Euclidean recursion. -/
structure RawGcdMachineState where
  dividend : Nat
  divisor : Nat
  deriving DecidableEq, Repr

/-- One nonterminal Euclidean transition, including the reduction machine
that computes the exact next remainder. -/
inductive RawGcdMachineStep :
    RawGcdMachineState → Nat → RawGcdMachineState → Prop where
  | remainder (a d : Nat)
      (hremainder : RawReductionMachineExec (d + 2) (Nat.log2 (d + 2))
        ⟨Nat.log2 a + 1, a⟩
        (rawPolynomialRemainderBitCosted a (d + 2)).1
        (rawPolynomialRemainderBitCosted a (d + 2)).2) :
      RawGcdMachineStep ⟨a, d + 2⟩
        (rawNatBitWidth (d + 2) +
          (rawPolynomialRemainderBitCosted a (d + 2)).2)
        ⟨d + 2, (rawPolynomialRemainderBitCosted a (d + 2)).1⟩

/-- Multi-step Euclidean execution, with the two actual base cases and a
recursive remainder transition for every divisor at least two. -/
inductive RawGcdMachineExec :
    RawGcdMachineState → Nat → Nat → Prop where
  | divisorZero (a : Nat) :
      RawGcdMachineExec ⟨a, 0⟩ a (rawNatBitWidth 0)
  | divisorOne (a : Nat) :
      RawGcdMachineExec ⟨a, 1⟩ 1 (rawNatBitWidth 1)
  | recurse (d a output tailCharge : Nat)
      (hstep : RawGcdMachineStep ⟨a, d + 2⟩
        (rawNatBitWidth (d + 2) +
          (rawPolynomialRemainderBitCosted a (d + 2)).2)
        ⟨d + 2, (rawPolynomialRemainderBitCosted a (d + 2)).1⟩)
      (htail : RawGcdMachineExec
        ⟨d + 2, (rawPolynomialRemainderBitCosted a (d + 2)).1⟩
        output tailCharge) :
      RawGcdMachineExec ⟨a, d + 2⟩ output
        (rawNatBitWidth (d + 2) +
          (rawPolynomialRemainderBitCosted a (d + 2)).2 + tailCharge)

/-- Every GCD machine execution computes exactly the paired Euclidean source
recurrence, including its declared charge. -/
theorem rawGcdMachineExec_sound
    {state : RawGcdMachineState} {output charge : Nat}
    (hexec : RawGcdMachineExec state output charge) :
    rawPolynomialGcdBitCosted state.dividend state.divisor = (output, charge) := by
  induction hexec with
  | divisorZero a => simp [rawPolynomialGcdBitCosted]
  | divisorOne a => simp [rawPolynomialGcdBitCosted]
  | recurse d a output tailCharge _ _ ih =>
      simp [rawPolynomialGcdBitCosted, ih]

/-- For every input, the exact costed Euclidean recurrence has a machine
execution whose output and total declared charge agree with its result. -/
theorem rawGcdMachineExec_exists
    (dividend divisor : Nat) :
    RawGcdMachineExec ⟨dividend, divisor⟩
      (rawPolynomialGcdBitCosted dividend divisor).1
      (rawPolynomialGcdBitCosted dividend divisor).2 := by
  induction divisor using Nat.strong_induction_on generalizing dividend with
  | h divisor ih =>
      cases divisor with
      | zero =>
          simpa [rawPolynomialGcdBitCosted] using
            (RawGcdMachineExec.divisorZero dividend)
      | succ divisor =>
          cases divisor with
          | zero =>
              simpa [rawPolynomialGcdBitCosted] using
                (RawGcdMachineExec.divisorOne dividend)
          | succ d =>
              let rem := rawPolynomialRemainderBitCosted dividend (d + 2)
              have hmodZero : d + 2 ≠ 0 := by omega
              have hremLt : rem.1 < d + 2 := by
                rw [show rem.1 = rawPolynomialRemainder dividend (d + 2) by
                  dsimp [rem]
                  exact rawPolynomialRemainderBitCosted_fst dividend (d + 2)]
                exact rawPolynomialRemainder_lt hmodZero
              have hmodOne : d + 2 ≠ 1 := by omega
              have hreduce : RawReductionMachineExec (d + 2)
                  (Nat.log2 (d + 2))
                  ⟨Nat.log2 dividend + 1, dividend⟩ rem.1 rem.2 := by
                simpa [rem, rawPolynomialRemainderBitCosted,
                  hmodZero, hmodOne] using
                  (rawReduceFuelBitCosted_has_machine_execution
                    (d + 2) (Nat.log2 (d + 2))
                    (Nat.log2 dividend + 1) dividend)
              have hstep : RawGcdMachineStep ⟨dividend, d + 2⟩
                  (rawNatBitWidth (d + 2) + rem.2) ⟨d + 2, rem.1⟩ := by
                simpa [rem] using
                  (RawGcdMachineStep.remainder dividend d hreduce)
              have htail := ih rem.1 hremLt (d + 2)
              simpa [rawPolynomialGcdBitCosted, rem] using
                (RawGcdMachineExec.recurse d dividend
                  (rawPolynomialGcdBitCosted (d + 2) rem.1).1
                  (rawPolynomialGcdBitCosted (d + 2) rem.1).2
                  hstep htail)

/-- Machine executions refine the uninstrumented Nat-mask GCD output. -/
theorem rawGcdMachineExec_refines_rawPolynomialGcd
    {state : RawGcdMachineState} {output charge : Nat}
    (hexec : RawGcdMachineExec state output charge) :
    output = rawPolynomialGcd state.dividend state.divisor := by
  have h := rawGcdMachineExec_sound hexec
  have hfst := congrArg Prod.fst h
  exact hfst.symm.trans
    (rawPolynomialGcdBitCosted_fst state.dividend state.divisor)

/-- Under the proved input-width envelope, every Euclidean machine execution
inherits the polynomial-times-log declared-charge bound for its recurrence. -/
theorem rawGcdMachineExec_charge_le
    {state : RawGcdMachineState} {output charge A : Nat}
    (hA : 0 < A) (ha : state.dividend < 2 ^ A)
    (hb : state.divisor < 2 ^ A)
    (hexec : RawGcdMachineExec state output charge) :
    charge ≤ (Nat.log2 state.divisor + 2) *
      (40 * (3 * A + 6) ^ 2 * (A + 1)) := by
  have hsound := rawGcdMachineExec_sound hexec
  have hcharge : charge =
      (rawPolynomialGcdBitCosted state.dividend state.divisor).2 := by
    have h := congrArg Prod.snd hsound
    exact h.symm
  rw [hcharge]
  exact rawPolynomialGcdBitCosted_cost_le
    hA ha hb

end CorruptedFieldRecovery
