import CorruptedFieldRecovery.RawRabinFrobeniusBitCost
import CorruptedFieldRecovery.RawRabinScan

/-! Costed execution of the actual repeated-Frobenius/GCD scan used by the
fast Rabin candidate gate. -/

namespace CorruptedFieldRecovery

private theorem rawRabinXor_lt_two_pow {a b k : Nat}
    (ha : a < 2 ^ k) (hb : b < 2 ^ k) : Nat.xor a b < 2 ^ k := by
  apply Nat.lt_of_testBit k
  · have haTop := Nat.testBit_eq_false_of_lt ha
    have hbTop := Nat.testBit_eq_false_of_lt hb
    simp [Nat.testBit_xor, haTop, hbTop]
  · simp
  · intro j hj
    have hpow : 2 ^ k ≤ 2 ^ j :=
      Nat.pow_le_pow_right (by decide : 0 < 2) hj.le
    have haAbove := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha hpow)
    have hbAbove := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb hpow)
    simp [Nat.testBit_xor, haAbove, hbAbove,
      Nat.testBit_two_pow_of_ne (Ne.symm (ne_of_gt hj))]

/-- Costed execution of one degree-`d` Rabin predicate: compute the actual
repeated-square Frobenius mask, XOR with `X`, then run the actual mask GCD. -/
def rawRabinCheckIndexBitCosted (modulus d : Nat) : Bool × Nat :=
  let frob := rawCandidateFrobeniusAuxBitCosted modulus d 2
  let argument := Nat.xor frob.1 2
  let gcd := rawPolynomialGcdBitCosted modulus argument
  (decide (gcd.1 = 1),
    frob.2 + gcd.2 + rawNatBitWidth modulus + rawNatBitWidth argument)

/-- The instrumented degree check returns the exact executable Rabin predicate. -/
theorem rawRabinCheckIndexBitCosted_fst (modulus d : Nat) :
    (rawRabinCheckIndexBitCosted modulus d).1 =
      decide (rawPolynomialGcd modulus
        (Nat.xor (rawCandidateFrobeniusAux modulus d 2) 2) = 1) := by
  simp [rawRabinCheckIndexBitCosted,
    rawCandidateFrobeniusAuxBitCosted_fst,
    rawPolynomialGcdBitCosted_fst]

/-- One scan over `q` possible factor degrees. The recursive order is reversed
from `List.range`, but the checked Boolean conjunction is commutative. -/
def rawRabinScanBitCosted (modulus : Nat) : Nat → Bool × Nat
  | 0 => (true, 0)
  | q + 1 =>
      let step := rawRabinCheckIndexBitCosted modulus (q + 1)
      let rest := rawRabinScanBitCosted modulus q
      (step.1 && rest.1, step.2 + rest.2)

/-- A common explicit per-check charge envelope when modulus and states fit in
`W` bits. The GCD inputs are bounded by `2W` bits even after the final XOR. -/
def rawRabinCheckIndexCharge (W d : Nat) : Nat :=
  d * rawRabinFrobeniusStepCharge W +
    (2 * W + 2) *
      (40 * (3 * (2 * W) + 6) ^ 2 * (2 * W + 1)) + 4 * W

/-- Each degree check's declared charge is bounded using the proved
Frobenius-loop and Euclidean-GCD recurrences. -/
theorem rawRabinCheckIndexBitCosted_cost_le
    {modulus d W : Nat} (hmod : modulus ≠ 0) (hmodOne : 1 < modulus)
    (hmodWidth : modulus < 2 ^ W) (hW : 2 ≤ W) :
    (rawRabinCheckIndexBitCosted modulus d).2 ≤
      rawRabinCheckIndexCharge W d := by
  let frob := rawCandidateFrobeniusAuxBitCosted modulus d 2
  let argument := Nat.xor frob.1 2
  let gcd := rawPolynomialGcdBitCosted modulus argument
  have htwoW : 2 < 2 ^ W := by
    have hpow : 2 ^ 2 ≤ 2 ^ W :=
      Nat.pow_le_pow_right (by decide : 0 < 2) hW
    norm_num at hpow ⊢
    omega
  have hfrobWidth : frob.1 < 2 ^ W := by
    simpa [frob] using
      rawCandidateFrobeniusAuxBitCosted_lt_pow hmod hmodWidth (by omega : 2 < 2 ^ W)
  have hargWidth : argument < 2 ^ (2 * W) := by
    have harg := rawRabinXor_lt_two_pow hfrobWidth htwoW
    exact lt_of_lt_of_le harg (by
      apply Nat.pow_le_pow_right (by decide : 0 < 2)
      omega)
  have hmodWidth' : modulus < 2 ^ (2 * W) := by
    exact lt_of_lt_of_le hmodWidth (by
      apply Nat.pow_le_pow_right (by decide : 0 < 2)
      omega)
  have hgcdCost := rawPolynomialGcdBitCosted_cost_le
    (by omega : 0 < 2 * W) hmodWidth' hargWidth
  have hlogArg : Nat.log2 argument < 2 * W :=
    rawLog2_lt_of_lt_pow (by omega) hargWidth
  have hgcdBound : gcd.2 ≤
      (2 * W + 2) *
        (40 * (3 * (2 * W) + 6) ^ 2 * (2 * W + 1)) := by
    have hgcdCost' : gcd.2 ≤
        (Nat.log2 argument + 2) *
          (40 * (3 * (2 * W) + 6) ^ 2 * (2 * W + 1)) := by
      simpa [gcd, Nat.add_comm] using hgcdCost
    exact le_trans hgcdCost'
      (Nat.mul_le_mul_right _ (by omega))
  have hfrobCost : frob.2 ≤ d * rawRabinFrobeniusStepCharge W := by
    simpa [frob] using
      rawCandidateFrobeniusAuxBitCosted_cost_le
        (modulus := modulus) (d := d) (x := 2) (W := W)
        hmod hmodOne hmodWidth (by omega : 0 < W) htwoW
  have hwidthMod : rawNatBitWidth modulus ≤ 2 * W := by
    unfold rawNatBitWidth
    have hlogMod := rawLog2_lt_of_lt_pow (by omega : 0 < 2 * W) hmodWidth'
    omega
  have hwidthArg : rawNatBitWidth argument ≤ 2 * W := by
    unfold rawNatBitWidth
    omega
  change frob.2 + gcd.2 + rawNatBitWidth modulus +
      rawNatBitWidth argument ≤ rawRabinCheckIndexCharge W d
  unfold rawRabinCheckIndexCharge
  omega

/-- The entire bounded scan's charge is at most the number of checks times a
uniform per-check bound using the largest tested degree. -/
theorem rawRabinScanBitCosted_cost_le
    {modulus q W : Nat} (hmod : modulus ≠ 0) (hmodOne : 1 < modulus)
    (hmodWidth : modulus < 2 ^ W) (hW : 2 ≤ W) :
    (rawRabinScanBitCosted modulus q).2 ≤
      q * (q * rawRabinFrobeniusStepCharge W +
        (2 * W + 2) *
          (40 * (3 * (2 * W) + 6) ^ 2 * (2 * W + 1)) + 4 * W) := by
  induction q with
  | zero => simp [rawRabinScanBitCosted]
  | succ q ih =>
      have hstep := rawRabinCheckIndexBitCosted_cost_le
        hmod hmodOne hmodWidth hW (d := q + 1)
      have hstep' :
          (rawRabinCheckIndexBitCosted modulus (q + 1)).2 ≤
            (q + 1) * rawRabinFrobeniusStepCharge W +
              (2 * W + 2) *
                (40 * (3 * (2 * W) + 6) ^ 2 * (2 * W + 1)) + 4 * W := by
        simpa [rawRabinCheckIndexCharge] using hstep
      have hrest := ih
      simp only [rawRabinScanBitCosted]
      change (rawRabinCheckIndexBitCosted modulus (q + 1)).2 +
          (rawRabinScanBitCosted modulus q).2 ≤
        (q + 1) * ((q + 1) * rawRabinFrobeniusStepCharge W +
          (2 * W + 2) *
            (40 * (3 * (2 * W) + 6) ^ 2 * (2 * W + 1)) + 4 * W)
      calc
        _ ≤ ((q + 1) * rawRabinFrobeniusStepCharge W +
              (2 * W + 2) *
                (40 * (3 * (2 * W) + 6) ^ 2 * (2 * W + 1)) + 4 * W) +
            q * (q * rawRabinFrobeniusStepCharge W +
              (2 * W + 2) *
                (40 * (3 * (2 * W) + 6) ^ 2 * (2 * W + 1)) + 4 * W) := by
                  exact Nat.add_le_add hstep' hrest
        _ ≤ _ := by nlinarith [Nat.zero_le q]

end CorruptedFieldRecovery
