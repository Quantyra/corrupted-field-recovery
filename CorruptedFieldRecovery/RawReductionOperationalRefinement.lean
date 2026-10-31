import CorruptedFieldRecovery.RawReductionOperationalMachine
import CorruptedFieldRecovery.RawReductionBitCostBounds

/-! Soundness and declared-charge bounds for the abstract reduction machine.
These results refine its small-step executions to the source recurrence and
transfer the already-proved polynomial charge envelope. They do not bound
compiled machine instructions, Lean runtime, or heap usage. -/

namespace CorruptedFieldRecovery

/-- Every derivation of the reduction machine computes exactly the paired
source recurrence, including its declared charge. -/
theorem rawReductionMachineExec_sound
    {modulus degree output charge : Nat}
    {state : RawReductionMachineState}
    (hexec : RawReductionMachineExec modulus degree state output charge) :
    rawReduceFuelBitCosted modulus degree state.fuel state.current =
      (output, charge) := by
  induction hexec with
  | fuelZero current =>
      rfl
  | stop fuel current hsmall =>
      simp [rawReduceFuelBitCosted, hsmall]
  | cancel fuel current output restCharge hlarge _ htail ih =>
      simp [rawReduceFuelBitCosted, hlarge, ih]

/-- The modeled operational semantics is deterministic in both result and
declared charge. -/
theorem rawReductionMachineExec_deterministic
    {modulus degree fuel current output₁ output₂ charge₁ charge₂ : Nat}
    (h₁ : RawReductionMachineExec modulus degree
      ⟨fuel, current⟩ output₁ charge₁)
    (h₂ : RawReductionMachineExec modulus degree
      ⟨fuel, current⟩ output₂ charge₂) :
    output₁ = output₂ ∧ charge₁ = charge₂ := by
  have e₁ := rawReductionMachineExec_sound h₁
  have e₂ := rawReductionMachineExec_sound h₂
  have e := e₁.symm.trans e₂
  cases e
  exact ⟨rfl, rfl⟩

/-- Under the proved modulus band and input-width premise, every machine
execution's total label charge obeys the existing polynomial-in-width
envelope for the exact reduction recurrence. -/
theorem rawReductionMachineExec_charge_le_of_modulus_band
    {modulus degree W fuel current output charge : Nat}
    (hmodLower : 2 ^ degree ≤ modulus)
    (hmodUpper : modulus < 2 ^ (degree + 1))
    (hW : 0 < W) (hcurrent : current < 2 ^ W)
    (hexec : RawReductionMachineExec modulus degree
      ⟨fuel, current⟩ output charge) :
    charge ≤ fuel * (40 * (W + degree + rawNatBitWidth degree + 4) ^ 2) := by
  have hsound := rawReductionMachineExec_sound hexec
  have hcharge : charge =
      (rawReduceFuelBitCosted modulus degree fuel current).2 := by
    have h := congrArg Prod.snd hsound
    exact h.symm
  rw [hcharge]
  exact rawReduceFuelBitCosted_cost_le_of_modulus_band
    degree modulus W fuel current hmodLower hmodUpper hW hcurrent

end CorruptedFieldRecovery
