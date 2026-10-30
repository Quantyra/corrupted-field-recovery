import CorruptedFieldRecovery.RawCandidateVerifierEnvelope

/-! Expand the declared scan charge to a single polynomial in candidate
degree and input widths. This is still the stated bit-operation model, not a
Lean compiler or processor runtime theorem. -/

namespace CorruptedFieldRecovery

set_option maxHeartbeats 1000000 in
/-- The per-degree uniform charge is quartic in `W + q + 1`, where `q` bounds
the tested degree. -/
theorem rawRabinScanUniformCharge_le {W q : Nat} :
    rawRabinScanUniformCharge W q ≤ 100000 * (W + q + 1) ^ 4 := by
  let r := W + q + 1
  have hr : 1 ≤ r := by dsimp [r]; omega
  have hW : W ≤ r := by dsimp [r]; omega
  have hq : q ≤ r := by dsimp [r]; omega
  have h2 : 2 * W + 2 ≤ 4 * r := by omega
  have hW1 : W + 1 ≤ 2 * r := by omega
  have h4 : 4 * W + 4 ≤ 8 * r := by omega
  have h6 : 6 * W + 6 ≤ 12 * r := by omega
  have h2W1 : 2 * W + 1 ≤ 3 * r := by omega
  have hWpow : (4 * W + 4) ^ 2 ≤ (8 * r) ^ 2 :=
    Nat.pow_le_pow_left h4 2
  have h6pow : (6 * W + 6) ^ 2 ≤ (12 * r) ^ 2 :=
    Nat.pow_le_pow_left h6 2
  have hqR3 : q * r ^ 3 ≤ r ^ 4 := by
    calc
      q * r ^ 3 ≤ r * r ^ 3 := Nat.mul_le_mul_right _ hq
      _ = r ^ 4 := by ring
  have hstep : rawRabinFrobeniusStepCharge W ≤ 6000 * r ^ 3 := by
    unfold rawRabinFrobeniusStepCharge
    nlinarith [Nat.mul_le_mul h2 hW1,
      Nat.mul_le_mul (show 2 * W ≤ 2 * r by omega) hWpow]
  have hstepTotal : q * rawRabinFrobeniusStepCharge W ≤ 6000 * r ^ 4 := by
    calc
      q * rawRabinFrobeniusStepCharge W ≤ q * (6000 * r ^ 3) :=
        Nat.mul_le_mul_left q hstep
      _ = 6000 * (q * r ^ 3) := by ring
      _ ≤ 6000 * r ^ 4 := Nat.mul_le_mul_left _ hqR3
  have hdivBase : 40 * (6 * W + 6) ^ 2 ≤ 40 * (12 * r) ^ 2 :=
    Nat.mul_le_mul_left 40 h6pow
  have hdivInner :
      40 * (6 * W + 6) ^ 2 * (2 * W + 1) ≤
        40 * (12 * r) ^ 2 * (3 * r) :=
    Nat.mul_le_mul hdivBase h2W1
  have hdivTotal : (2 * W + 2) *
      (40 * (6 * W + 6) ^ 2 * (2 * W + 1)) ≤
      69120 * r ^ 4 := by
    calc
      _ ≤ (4 * r) * (40 * (12 * r) ^ 2 * (3 * r)) :=
        Nat.mul_le_mul h2 hdivInner
      _ = 69120 * r ^ 4 := by ring
  have hrleR4 : r ≤ r ^ 4 :=
    by
      simpa only [pow_one] using
        (Nat.pow_le_pow_right (by omega : 0 < r) (by decide : 1 ≤ 4))
  have hWleR4 : W ≤ r ^ 4 := le_trans hW hrleR4
  unfold rawRabinScanUniformCharge
  calc
    q * rawRabinFrobeniusStepCharge W +
        (2 * W + 2) * (40 * (3 * (2 * W) + 6) ^ 2 * (2 * W + 1)) +
        4 * W ≤ 6000 * r ^ 4 + 69120 * r ^ 4 + 4 * r ^ 4 := by
          have h4W : 4 * W ≤ 4 * r ^ 4 := Nat.mul_le_mul_left 4 hWleR4
          nlinarith [hstepTotal, hdivTotal, h4W]
    _ ≤ 100000 * r ^ 4 := by omega

/-- The full fast verifier has a fifth-degree declared-charge envelope in
`s + modulus.size + scalar.size + 4`, covering both shape rejection and
successful shape followed by range construction and the short-circuit scan. -/
theorem rawFieldCandidateFastCheckFullBitCosted_degree_five_bound {s : Nat}
    (candidate : RawFieldCandidate s) :
    (rawFieldCandidateFastCheckFullBitCosted candidate).2 ≤
      2000000 *
        (s + candidate.modulus.size + candidate.scalar.size + 4) ^ 5 := by
  let q := s / 2
  let b := s + candidate.modulus.size + candidate.scalar.size + 4
  let r := (s + 1) + q + 1
  have hb : 4 ≤ b := by dsimp [b]; omega
  have hq : q ≤ b := by dsimp [q, b]; omega
  have hr : r ≤ 2 * b := by
    dsimp [r, q, b]
    omega
  have hrpow : r ^ 4 ≤ (2 * b) ^ 4 := Nat.pow_le_pow_left hr 4
  have hcharge := rawRabinScanUniformCharge_le (W := s + 1) (q := q)
  have hchargeMul := Nat.mul_le_mul_left q hcharge
  have hscan : q * rawRabinScanUniformCharge (s + 1) q ≤
      1600000 * b ^ 5 := by
    have hprod := Nat.mul_le_mul hq hrpow
    calc
      q * rawRabinScanUniformCharge (s + 1) q ≤ q * (100000 * r ^ 4) := by
        exact hchargeMul
      _ = 100000 * (q * r ^ 4) := by ring
      _ ≤ 100000 * (b * (2 * b) ^ 4) := Nat.mul_le_mul_left _ hprod
      _ = 1600000 * b ^ 5 := by ring
  have hshape := rawFieldCandidateFastCheckFullBitCosted_polynomial_envelope candidate
  have hqSq : q ^ 2 ≤ b ^ 2 := Nat.pow_le_pow_left hq 2
  have hb2le5 : b ^ 2 ≤ b ^ 5 :=
    Nat.pow_le_pow_right (by omega : 1 ≤ b) (by omega)
  have hqSq5 : q ^ 2 ≤ b ^ 5 := le_trans hqSq hb2le5
  have hb2 : b ^ 2 ≤ b ^ 5 := by
    exact Nat.pow_le_pow_right (by omega : 1 ≤ b) (by omega)
  calc
    _ ≤ 100 * b ^ 2 + q ^ 2 + q *
        rawRabinScanUniformCharge (s + 1) q := by
          simpa [q, b] using hshape
    _ ≤ 100 * b ^ 2 + b ^ 5 + 1600000 * b ^ 5 :=
          Nat.add_le_add (Nat.add_le_add le_rfl hqSq5) hscan
    _ ≤ 2000000 * b ^ 5 := by nlinarith [hb2]

end CorruptedFieldRecovery
