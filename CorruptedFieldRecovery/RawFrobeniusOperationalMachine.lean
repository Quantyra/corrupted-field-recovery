import CorruptedFieldRecovery.RawReductionOperationalMachine
import CorruptedFieldRecovery.RawRabinFrobeniusBitCost

/-! A high-level small-step machine for the repeated-square Frobenius loop.
Each iteration uses the existing costed Nat multiplication and includes an
actual execution witness for the fuel-bounded reduction subcall. The charge is
the declared algorithmic charge; multiplication remains an instrumented
primitive here, and this is not Lean or compiled-machine runtime semantics. -/

namespace CorruptedFieldRecovery

/-- Control state for repeated-square quotient computation. -/
structure RawFrobeniusMachineState where
  iterations : Nat
  current : Nat
  deriving DecidableEq, Repr

/-- One Frobenius iteration: square the current mask, then execute the exact
remainder machine on the square. -/
inductive RawFrobeniusMachineStep (modulus : Nat) :
    RawFrobeniusMachineState → Nat → RawFrobeniusMachineState → Prop where
  | squareReduce (iterations current : Nat)
      (hremainder : RawReductionMachineExec modulus (Nat.log2 modulus)
        ⟨Nat.log2 (rawPolyMulBitCosted current current).1 + 1,
          (rawPolyMulBitCosted current current).1⟩
        (rawPolynomialRemainderBitCosted
          (rawPolyMulBitCosted current current).1 modulus).1
        (rawPolynomialRemainderBitCosted
          (rawPolyMulBitCosted current current).1 modulus).2) :
      RawFrobeniusMachineStep modulus
        ⟨iterations + 1, current⟩
        ((rawPolyMulBitCosted current current).2 +
          (rawPolynomialRemainderBitCosted
            (rawPolyMulBitCosted current current).1 modulus).2 +
          rawNatBitWidth modulus + rawNatBitWidth current)
        ⟨iterations,
          (rawPolynomialRemainderBitCosted
            (rawPolyMulBitCosted current current).1 modulus).1⟩

/-- Multi-iteration execution of the Frobenius machine, composed from the
square/reduce transition and a recursive execution of the remaining loop. -/
inductive RawFrobeniusMachineExec (modulus : Nat) :
    RawFrobeniusMachineState → Nat → Nat → Prop where
  | done (current : Nat) :
      RawFrobeniusMachineExec modulus ⟨0, current⟩ current 0
  | iterate (iterations current output tailCharge : Nat)
      (hstep : RawFrobeniusMachineStep modulus
        ⟨iterations + 1, current⟩
        ((rawPolyMulBitCosted current current).2 +
          (rawPolynomialRemainderBitCosted
            (rawPolyMulBitCosted current current).1 modulus).2 +
          rawNatBitWidth modulus + rawNatBitWidth current)
        ⟨iterations,
          (rawPolynomialRemainderBitCosted
            (rawPolyMulBitCosted current current).1 modulus).1⟩)
      (htail : RawFrobeniusMachineExec modulus
        ⟨iterations,
          (rawPolynomialRemainderBitCosted
            (rawPolyMulBitCosted current current).1 modulus).1⟩
        output tailCharge) :
      RawFrobeniusMachineExec modulus ⟨iterations + 1, current⟩ output
        ((rawPolyMulBitCosted current current).2 +
          (rawPolynomialRemainderBitCosted
            (rawPolyMulBitCosted current current).1 modulus).2 +
          rawNatBitWidth modulus + rawNatBitWidth current + tailCharge)

/-- Each successful execution computes exactly the existing instrumented
repeated-square recurrence and its declared charge. -/
theorem rawFrobeniusMachineExec_sound
    {modulus output charge : Nat} {state : RawFrobeniusMachineState}
    (hexec : RawFrobeniusMachineExec modulus state output charge) :
    rawCandidateFrobeniusAuxBitCosted modulus state.iterations state.current =
      (output, charge) := by
  induction hexec with
  | done current => rfl
  | iterate iterations current output tailCharge hstep htail ih =>
      simp [rawCandidateFrobeniusAuxBitCosted, ih]

/-- For modulus greater than one, every costed Frobenius recurrence has an
execution: each iteration includes a witness for the actual remainder
subroutine's reduction-machine execution. -/
theorem rawFrobeniusMachineExec_exists
    (modulus iterations current : Nat) (hmodOne : 1 < modulus) :
    RawFrobeniusMachineExec modulus ⟨iterations, current⟩
      (rawCandidateFrobeniusAuxBitCosted modulus iterations current).1
      (rawCandidateFrobeniusAuxBitCosted modulus iterations current).2 := by
  induction iterations generalizing current with
  | zero =>
      simpa [rawCandidateFrobeniusAuxBitCosted] using
        (RawFrobeniusMachineExec.done (modulus := modulus) current)
  | succ iterations ih =>
      let square := rawPolyMulBitCosted current current
      let rem := rawPolynomialRemainderBitCosted square.1 modulus
      have hmodZero : modulus ≠ 0 := by omega
      have hmodUnit : modulus ≠ 1 := by omega
      have hreduce : RawReductionMachineExec modulus (Nat.log2 modulus)
          ⟨Nat.log2 square.1 + 1, square.1⟩ rem.1 rem.2 := by
        simpa [rem, square, rawPolynomialRemainderBitCosted,
          hmodZero, hmodUnit] using
          (rawReduceFuelBitCosted_has_machine_execution modulus
            (Nat.log2 modulus) (Nat.log2 square.1 + 1) square.1)
      have hstep : RawFrobeniusMachineStep modulus
          ⟨iterations + 1, current⟩
          (square.2 + rem.2 + rawNatBitWidth modulus +
            rawNatBitWidth current)
          ⟨iterations, rem.1⟩ := by
        simpa [square, rem] using
          (RawFrobeniusMachineStep.squareReduce (modulus := modulus)
            iterations current hreduce)
      have htail := ih rem.1
      simpa [rawCandidateFrobeniusAuxBitCosted, square, rem] using
        (RawFrobeniusMachineExec.iterate (modulus := modulus)
          iterations current
          (rawCandidateFrobeniusAuxBitCosted modulus iterations rem.1).1
          (rawCandidateFrobeniusAuxBitCosted modulus iterations rem.1).2
          hstep htail)

/-- The operational execution refines to the uninstrumented Frobenius mask. -/
theorem rawFrobeniusMachineExec_refines_rawCandidateFrobeniusAux
    {modulus iterations current output charge : Nat}
    (hexec : RawFrobeniusMachineExec modulus ⟨iterations, current⟩
      output charge) :
    output = rawCandidateFrobeniusAux modulus iterations current := by
  have h := rawFrobeniusMachineExec_sound hexec
  have hfst := congrArg Prod.fst h
  exact hfst.symm.trans (rawCandidateFrobeniusAuxBitCosted_fst
    modulus iterations current)

/-- The execution charge inherits the accepted cubic-per-iteration bound
under the same modulus and representative-width hypotheses. -/
theorem rawFrobeniusMachineExec_charge_le
    {modulus iterations current output charge W : Nat}
    (hmod : modulus ≠ 0) (hmodOne : 1 < modulus)
    (hmodWidth : modulus < 2 ^ W) (hW : 0 < W)
    (hcurrent : current < 2 ^ W)
    (hexec : RawFrobeniusMachineExec modulus ⟨iterations, current⟩
      output charge) :
    charge ≤ iterations * rawRabinFrobeniusStepCharge W := by
  have hsound := rawFrobeniusMachineExec_sound hexec
  have hcharge : charge =
      (rawCandidateFrobeniusAuxBitCosted modulus iterations current).2 := by
    have h := congrArg Prod.snd hsound
    exact h.symm
  rw [hcharge]
  exact rawCandidateFrobeniusAuxBitCosted_cost_le
    hmod hmodOne hmodWidth hW hcurrent

end CorruptedFieldRecovery
