import CorruptedFieldRecovery.RawFrobeniusOperationalMachine
import CorruptedFieldRecovery.RawGcdOperationalMachine
import CorruptedFieldRecovery.RawRabinScanBitCost

/-! A one-index Rabin execution composed from the accepted Frobenius and
Euclidean GCD machines. The Frobenius subexecution includes reducer-machine
witnesses; the GCD subexecution includes its remainder-machine witnesses.
The outer index check composes their declared charges and exact mask values.
This file does not yet model the surrounding List.range/short-circuit scan,
the internals of multiplication, or Lean/compiled-machine runtime and heap. -/

namespace CorruptedFieldRecovery

/-- A successful execution of one Rabin degree check consists of a repeated
square/reduce machine run followed by a Euclidean GCD machine run on the
resulting XOR argument. -/
inductive RawRabinIndexMachineExec (modulus degree : Nat) :
    Bool → Nat → Prop where
  | check (frobValue frobCharge gcdValue gcdCharge : Nat)
      (hfrobenius : RawFrobeniusMachineExec modulus
        ⟨degree, 2⟩ frobValue frobCharge)
      (hgcd : RawGcdMachineExec
        ⟨modulus, Nat.xor frobValue 2⟩ gcdValue gcdCharge) :
      RawRabinIndexMachineExec modulus degree
        (decide (gcdValue = 1))
        (frobCharge + gcdCharge + rawNatBitWidth modulus +
          rawNatBitWidth (Nat.xor frobValue 2))

/-- Every composed index-machine execution agrees with the existing costed
one-degree Rabin check, in both Boolean result and declared charge. -/
theorem rawRabinIndexMachineExec_sound
    {modulus degree : Nat} {result : Bool} {charge : Nat}
    (hexec : RawRabinIndexMachineExec modulus degree result charge) :
    rawRabinCheckIndexBitCosted modulus degree = (result, charge) := by
  cases hexec with
  | check frobValue frobCharge gcdValue gcdCharge hfrobenius hgcd =>
      have hfrob : rawCandidateFrobeniusAuxBitCosted modulus degree 2 =
          (frobValue, frobCharge) := by
        simpa using rawFrobeniusMachineExec_sound hfrobenius
      have hgcd' : rawPolynomialGcdBitCosted modulus (Nat.xor frobValue 2) =
          (gcdValue, gcdCharge) := by
        simpa using rawGcdMachineExec_sound hgcd
      simp only [rawRabinCheckIndexBitCosted]
      rw [hfrob]
      dsimp only
      rw [hgcd']

/-- When the modulus exceeds one, the exact costed index check has a composed
machine execution. Its Frobenius half is available under this modulus
condition; the Euclidean GCD half handles all Nat inputs. -/
theorem rawRabinIndexMachineExec_exists
    (modulus degree : Nat) (hmodOne : 1 < modulus) :
    RawRabinIndexMachineExec modulus degree
      (rawRabinCheckIndexBitCosted modulus degree).1
      (rawRabinCheckIndexBitCosted modulus degree).2 := by
  let frob := rawCandidateFrobeniusAuxBitCosted modulus degree 2
  let argument := Nat.xor frob.1 2
  let gcd := rawPolynomialGcdBitCosted modulus argument
  have hfrobenius : RawFrobeniusMachineExec modulus
      ⟨degree, 2⟩ frob.1 frob.2 := by
    simpa [frob] using
      (rawFrobeniusMachineExec_exists modulus degree 2 hmodOne)
  have hgcd : RawGcdMachineExec ⟨modulus, argument⟩ gcd.1 gcd.2 := by
    simpa [gcd] using rawGcdMachineExec_exists modulus argument
  have hcheck := RawRabinIndexMachineExec.check
    (modulus := modulus) (degree := degree)
    frob.1 frob.2 gcd.1 gcd.2 hfrobenius hgcd
  simpa [rawRabinCheckIndexBitCosted, frob, argument, gcd] using hcheck

/-- The composed machine's Boolean is the literal Nat-mask Rabin predicate
used by the fast checker. -/
theorem rawRabinIndexMachineExec_refines_predicate
    {modulus degree : Nat} {result : Bool} {charge : Nat}
    (hexec : RawRabinIndexMachineExec modulus degree result charge) :
    result = decide (rawPolynomialGcd modulus
      (Nat.xor (rawCandidateFrobeniusAux modulus degree 2) 2) = 1) := by
  have hsound := rawRabinIndexMachineExec_sound hexec
  have hresult := congrArg Prod.fst hsound
  exact hresult.symm.trans
    (rawRabinCheckIndexBitCosted_fst modulus degree)

/-- Under the accepted modulus and width premises, a one-index machine run
inherits the existing explicit declared-charge envelope. -/
theorem rawRabinIndexMachineExec_charge_le
    {modulus degree W : Nat} {result : Bool} {charge : Nat}
    (hmod : modulus ≠ 0) (hmodOne : 1 < modulus)
    (hmodWidth : modulus < 2 ^ W) (hW : 2 ≤ W)
    (hexec : RawRabinIndexMachineExec modulus degree result charge) :
    charge ≤ rawRabinCheckIndexCharge W degree := by
  have hsound := rawRabinIndexMachineExec_sound hexec
  have hcharge : charge = (rawRabinCheckIndexBitCosted modulus degree).2 := by
    have h := congrArg Prod.snd hsound
    exact h.symm
  rw [hcharge]
  exact rawRabinCheckIndexBitCosted_cost_le hmod hmodOne hmodWidth hW

end CorruptedFieldRecovery
