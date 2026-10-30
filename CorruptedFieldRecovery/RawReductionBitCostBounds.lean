import CorruptedFieldRecovery.RawReductionBitCost

/-! Polynomial bounds for the declared reducer charge, assuming the proved
modulus power band. Every active cancellation lowers the representative's
logarithmic bit width by the accepted reduction-interval theorem. -/

namespace CorruptedFieldRecovery

private theorem rawBitWidth_le_of_lt_pow {n k : Nat}
    (hn : n < 2 ^ k) : rawNatBitWidth n ≤ k + 1 := by
  by_cases hn0 : n = 0
  · simp [rawNatBitWidth, hn0]
  · have hk : 0 < k := by
      cases k with
      | zero =>
          have hnzero : n = 0 := by norm_num at hn; omega
          exact False.elim (hn0 hnzero)
      | succ k => omega
    have hlog := rawLog2_lt_of_lt_pow hk hn
    unfold rawNatBitWidth
    omega

private theorem rawNatBitWidth_mul_le (a b : Nat) :
    rawNatBitWidth (a * b) ≤ rawNatBitWidth a + rawNatBitWidth b + 1 := by
  by_cases ha0 : a = 0
  · simp [ha0, rawNatBitWidth]
  by_cases hb0 : b = 0
  · simp [hb0, rawNatBitWidth]
  have ha : a < 2 ^ rawNatBitWidth a := by
    unfold rawNatBitWidth
    exact Nat.lt_log2_self
  have hb : b < 2 ^ rawNatBitWidth b := by
    unfold rawNatBitWidth
    exact Nat.lt_log2_self
  have hp : a * b < 2 ^ (rawNatBitWidth a + rawNatBitWidth b) := by
    calc
      a * b < 2 ^ rawNatBitWidth a * 2 ^ rawNatBitWidth b := by
        have h1 := Nat.mul_lt_mul_of_pos_right ha (Nat.pos_of_ne_zero hb0)
        have h2 := Nat.mul_lt_mul_of_pos_left hb
          (by positivity : 0 < 2 ^ rawNatBitWidth a)
        exact lt_trans h1 h2
      _ = 2 ^ (rawNatBitWidth a + rawNatBitWidth b) := by rw [pow_add]
  have hL : 0 < rawNatBitWidth a + rawNatBitWidth b := by
    unfold rawNatBitWidth
    omega
  have hlog := rawLog2_lt_of_lt_pow hL hp
  unfold rawNatBitWidth at hlog ⊢
  omega

/-- A reduction step's declared bit charge is quadratic in the modulus and
current-representative widths. -/
theorem rawReduceStepBitCosted_cost_le {degree modulus a W : Nat}
    (hmodUpper : modulus < 2 ^ (degree + 1))
    (hW : 0 < W) (ha : a < 2 ^ W) :
    (rawReduceStepBitCosted modulus degree a).2 ≤
      20 * (W + degree + rawNatBitWidth degree + 4) ^ 2 := by
  let z := W + degree + rawNatBitWidth degree + 4
  have hlog : Nat.log2 a < W := rawLog2_lt_of_lt_pow hW ha
  let shift := Nat.log2 a - degree
  let power := 2 ^ shift
  have hshift : shift ≤ W := by dsimp [shift]; omega
  have hpowerBound : power < 2 ^ (W + 1) := by
    dsimp [power]
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).2
    omega
  have hpowerWidth : rawNatBitWidth power ≤ W + 2 :=
    rawBitWidth_le_of_lt_pow hpowerBound
  have hmodWidth : rawNatBitWidth modulus ≤ degree + 2 :=
    rawBitWidth_le_of_lt_pow hmodUpper
  have hshiftedWidth : rawNatBitWidth (modulus * power) ≤
      rawNatBitWidth modulus + rawNatBitWidth power + 1 :=
    rawNatBitWidth_mul_le modulus power
  have hA : rawNatBitWidth a ≤ z := by
    exact le_trans (rawBitWidth_le_of_lt_pow ha) (by dsimp [z]; omega)
  have hD : rawNatBitWidth degree ≤ z := by dsimp [z]; omega
  have hP : rawNatBitWidth power ≤ z := by
    exact le_trans hpowerWidth (by dsimp [z]; omega)
  have hM : rawNatBitWidth modulus ≤ z :=
    le_trans hmodWidth (by dsimp [z]; omega)
  have hShifted : rawNatBitWidth (modulus * power) ≤ z := by
    have := hshiftedWidth
    dsimp [z] at this ⊢
    have hdegWidth : 1 ≤ rawNatBitWidth degree := by
      unfold rawNatBitWidth
      omega
    omega
  have hmul : rawNatMulBitCharge modulus power ≤ z * z := by
    unfold rawNatMulBitCharge
    exact Nat.mul_le_mul hM hP
  dsimp [rawReduceStepBitCosted, rawNatMulBitCharge, shift, power]
  have hcharge :
      1 + rawNatBitWidth a + rawNatBitWidth degree + rawNatBitWidth (2 ^ (Nat.log2 a - degree)) +
        rawNatBitWidth modulus * rawNatBitWidth (2 ^ (Nat.log2 a - degree)) +
        rawNatBitWidth a + rawNatBitWidth (modulus * 2 ^ (Nat.log2 a - degree)) ≤
      20 * z ^ 2 := by
    nlinarith [hA, hD, hP, hM, hShifted, hmul, show 4 ≤ z by dsimp [z]; omega]
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcharge

/-- Under the modulus-band hypotheses, an active reduction step preserves an
upper bound on the representative's bit width. -/
private theorem rawReduceStep_lt_pow_of_width {degree modulus a W : Nat}
    (hmodLower : 2 ^ degree ≤ modulus)
    (hmodUpper : modulus < 2 ^ (degree + 1))
    (hW : 0 < W) (ha : a < 2 ^ W)
    (hactive : 2 ^ degree ≤ a) :
    rawReduceStep modulus degree a < 2 ^ W := by
  have hstep := rawReduceStep_lt_pow_of_modulus_band
    degree modulus a hmodLower hmodUpper hactive
  have hlog : Nat.log2 a < W := rawLog2_lt_of_lt_pow hW ha
  have hpow : 2 ^ Nat.log2 a ≤ 2 ^ W := by
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hlog.le
  exact lt_of_lt_of_le hstep hpow

/-- The reducer's live representative stays within the supplied bit-width
bound throughout execution. This proves the space bound from the same modulus
band descent used by the cost argument. -/
theorem rawReduceFuel_lt_two_pow_of_modulus_band {degree modulus W fuel a : Nat}
    (hmodLower : 2 ^ degree ≤ modulus)
    (hmodUpper : modulus < 2 ^ (degree + 1))
    (hdegree : degree ≤ W) (hW : 0 < W) (ha : a < 2 ^ W) :
    rawReduceFuel modulus degree fuel a < 2 ^ W := by
  induction fuel generalizing a with
  | zero => exact ha
  | succ fuel ih =>
      by_cases hsmall : a < 2 ^ degree
      · rw [rawReduceFuel, if_pos hsmall]
        have hpow : 2 ^ degree ≤ 2 ^ W := by gcongr; norm_num
        exact lt_of_lt_of_le hsmall hpow
      · rw [rawReduceFuel, if_neg hsmall]
        have hstep := rawReduceStep_lt_pow_of_width
          hmodLower hmodUpper hW ha (Nat.le_of_not_gt hsmall)
        exact ih hstep

/-- Fuel-bounded reduction costs at most a cubic-in-width bound per fuel
budget in the declared model. The result size invariant is proved from the
actual cancellation theorem, not postulated. -/
theorem rawReduceFuelBitCosted_cost_le_of_modulus_band
    (degree modulus W fuel a : Nat)
    (hmodLower : 2 ^ degree ≤ modulus)
    (hmodUpper : modulus < 2 ^ (degree + 1))
    (hW : 0 < W) (ha : a < 2 ^ W) :
    (rawReduceFuelBitCosted modulus degree fuel a).2 ≤
      fuel * (40 * (W + degree + rawNatBitWidth degree + 4) ^ 2) := by
  induction fuel generalizing a with
  | zero => simp [rawReduceFuelBitCosted]
  | succ fuel ih =>
      by_cases hsmall : a < 2 ^ degree
      · have hA : rawNatBitWidth a ≤ W + 1 := rawBitWidth_le_of_lt_pow ha
        have hcmp : rawNatBitWidth a + degree + 1 ≤
            40 * (W + degree + rawNatBitWidth degree + 4) ^ 2 := by
          have hz : 4 ≤ W + degree + rawNatBitWidth degree + 4 := by omega
          nlinarith [hA, Nat.zero_le W, Nat.zero_le degree,
            Nat.zero_le (rawNatBitWidth degree)]
        simp only [rawReduceFuelBitCosted, if_pos hsmall]
        calc
          _ ≤ 40 * (W + degree + rawNatBitWidth degree + 4) ^ 2 := hcmp
          _ ≤ (fuel + 1) *
              (40 * (W + degree + rawNatBitWidth degree + 4) ^ 2) := by
                nlinarith
      · have hactive : 2 ^ degree ≤ a := Nat.le_of_not_gt hsmall
        have hstepWidth := rawReduceStep_lt_pow_of_width
          hmodLower hmodUpper hW ha hactive
        have hstepCharge := rawReduceStepBitCosted_cost_le
          hmodUpper hW ha
        have hcmp : rawNatBitWidth a + degree + 1 ≤
            20 * (W + degree + rawNatBitWidth degree + 4) ^ 2 := by
          have hA : rawNatBitWidth a ≤ W + 1 := rawBitWidth_le_of_lt_pow ha
          nlinarith [hA, Nat.zero_le W, Nat.zero_le degree,
            Nat.zero_le (rawNatBitWidth degree)]
        have hlocal : rawNatBitWidth a + degree + 1 +
            (rawReduceStepBitCosted modulus degree a).2 ≤
            40 * (W + degree + rawNatBitWidth degree + 4) ^ 2 := by
          nlinarith [hcmp, hstepCharge]
        have hrest := ih (rawReduceStepBitCosted modulus degree a).1 hstepWidth
        simp only [rawReduceFuelBitCosted, if_neg hsmall]
        nlinarith [hlocal, hrest]

end CorruptedFieldRecovery
