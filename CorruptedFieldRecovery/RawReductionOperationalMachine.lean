import CorruptedFieldRecovery.RawReductionBitCost

/-! A small-step abstract machine for the fuel-bounded XOR reduction routine.
Each transition is one nonterminal cancellation and carries exactly the
declared comparison-plus-cancellation charge. This is a mathematical
operational model of the source recurrence, not a claim about Lean's compiled
runtime, allocation, or physical bit instructions. -/

namespace CorruptedFieldRecovery

/-- Control state for one reduction call. -/
structure RawReductionMachineState where
  fuel : Nat
  current : Nat
  deriving DecidableEq, Repr

/-- One active cancellation step of the reducer. The transition consumes one
fuel unit and replaces the current representative by the exact instrumented
XOR cancellation result. Its label charges the test and the cancellation. -/
inductive RawReductionMachineStep (modulus degree : Nat) :
    RawReductionMachineState → Nat → RawReductionMachineState → Prop where
  | cancel (fuel current : Nat) (hlarge : ¬ current < 2 ^ degree) :
      RawReductionMachineStep modulus degree
        ⟨fuel + 1, current⟩
        (rawNatBitWidth current + degree + 1 +
          (rawReduceStepBitCosted modulus degree current).2)
        ⟨fuel, (rawReduceStepBitCosted modulus degree current).1⟩

/-- Multi-step execution of the reducer machine. Zero fuel and a successful
stop test are terminal; otherwise the execution must take the labelled
cancellation transition and continue from its successor state. -/
inductive RawReductionMachineExec (modulus degree : Nat) :
    RawReductionMachineState → Nat → Nat → Prop where
  | fuelZero (current : Nat) :
      RawReductionMachineExec modulus degree ⟨0, current⟩ current 0
  | stop (fuel current : Nat) (hsmall : current < 2 ^ degree) :
      RawReductionMachineExec modulus degree ⟨fuel + 1, current⟩ current
        (rawNatBitWidth current + degree + 1)
  | cancel (fuel current output restCharge : Nat)
      (hlarge : ¬ current < 2 ^ degree)
      (hstep : RawReductionMachineStep modulus degree
        ⟨fuel + 1, current⟩
        (rawNatBitWidth current + degree + 1 +
          (rawReduceStepBitCosted modulus degree current).2)
        ⟨fuel, (rawReduceStepBitCosted modulus degree current).1⟩)
      (htail : RawReductionMachineExec modulus degree
        ⟨fuel, (rawReduceStepBitCosted modulus degree current).1⟩
        output restCharge) :
      RawReductionMachineExec modulus degree ⟨fuel + 1, current⟩ output
        (rawNatBitWidth current + degree + 1 +
          (rawReduceStepBitCosted modulus degree current).2 + restCharge)

/-- The instrumented recursive reducer has a corresponding machine execution
whose output and total declared charge are exactly the returned pair. -/
theorem rawReduceFuelBitCosted_has_machine_execution
    (modulus degree fuel current : Nat) :
    RawReductionMachineExec modulus degree ⟨fuel, current⟩
      (rawReduceFuelBitCosted modulus degree fuel current).1
      (rawReduceFuelBitCosted modulus degree fuel current).2 := by
  induction fuel generalizing current with
  | zero =>
      simpa [rawReduceFuelBitCosted] using
        (RawReductionMachineExec.fuelZero (modulus := modulus)
          (degree := degree) current)
  | succ fuel ih =>
      by_cases hsmall : current < 2 ^ degree
      · simpa [rawReduceFuelBitCosted, hsmall] using
          (RawReductionMachineExec.stop (modulus := modulus)
            (degree := degree) fuel current hsmall)
      · let step := rawReduceStepBitCosted modulus degree current
        have hstep : RawReductionMachineStep modulus degree
            ⟨fuel + 1, current⟩
            (rawNatBitWidth current + degree + 1 + step.2)
            ⟨fuel, step.1⟩ := by
          simpa [step] using
            (RawReductionMachineStep.cancel (modulus := modulus)
              (degree := degree) fuel current hsmall)
        have htail := ih step.1
        simpa [rawReduceFuelBitCosted, hsmall, step] using
          (RawReductionMachineExec.cancel (modulus := modulus)
            (degree := degree) fuel current
            (rawReduceFuelBitCosted modulus degree fuel step.1).1
            (rawReduceFuelBitCosted modulus degree fuel step.1).2
            hsmall hstep htail)

/-- The same execution returns the uninstrumented reducer's exact result;
its transition labels still sum to the declared charge returned by the
instrumented recurrence. -/
theorem rawReduceFuelBitCosted_machine_refines_rawReduceFuel
    (modulus degree fuel current : Nat) :
    RawReductionMachineExec modulus degree ⟨fuel, current⟩
      (rawReduceFuel modulus degree fuel current)
      (rawReduceFuelBitCosted modulus degree fuel current).2 := by
  rw [← rawReduceFuelBitCosted_fst]
  exact rawReduceFuelBitCosted_has_machine_execution
    modulus degree fuel current

end CorruptedFieldRecovery
