import CorruptedFieldRecovery.RawArithmeticMulTraceWidth
import CorruptedFieldRecovery.RawReductionLogFuel

/-! Reachable activation frames for the fuel-bounded XOR reducer. The trace
follows the exact stop/step recursion. Its width theorem uses the accepted
modulus-band descent; it is an abstract register-space result, not a runtime
heap claim. -/

namespace CorruptedFieldRecovery

/-- Exponent large enough to represent every control value at most W. -/
def rawArithmeticParameterWidth (W : Nat) : Nat :=
  W + Nat.log2 (W + 1) + 1

private theorem rawArithmetic_le_pow_parameter {n W : Nat} (hn : n ≤ W) :
    n < 2 ^ rawArithmeticParameterWidth W := by
  have hlog : W + 1 < 2 ^ (Nat.log2 (W + 1) + 1) := Nat.lt_log2_self
  have hexp : Nat.log2 (W + 1) + 1 ≤ rawArithmeticParameterWidth W := by
    unfold rawArithmeticParameterWidth
    omega
  have hpow : 2 ^ (Nat.log2 (W + 1) + 1) ≤
      2 ^ rawArithmeticParameterWidth W :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hexp
  omega

private theorem rawArithmetic_width_lt_parameter {n W : Nat}
    (hn : n < 2 ^ W) :
    n < 2 ^ rawArithmeticParameterWidth W := by
  have hle : W ≤ rawArithmeticParameterWidth W := by
    unfold rawArithmeticParameterWidth
    omega
  exact lt_of_lt_of_le hn
    (Nat.pow_le_pow_right (by decide : 0 < 2) hle)

/-- All snapshots visited by the bounded reduction call. At a tested level,
the frame records the current operands and the shifted modulus/output; the
recursive tail is included only when the actual stop test is false. -/
def rawReduceFuelActivationTrace (modulus degree : Nat) :
    Nat → Nat → List RawArithmeticFrame
  | 0, a => [rawArithmeticReduceFrame modulus degree 0 a 0 a]
  | fuel + 1, a =>
      if a < 2 ^ degree then
        [rawArithmeticReduceFrame modulus degree (fuel + 1) a 0 a]
      else
        let power := 2 ^ (Nat.log2 a - degree)
        let shifted := modulus * power
        let step := rawReduceStepBitCosted modulus degree a
        rawArithmeticReduceFrame modulus degree (fuel + 1) a shifted step.1 ::
          rawReduceFuelActivationTrace modulus degree fuel step.1
termination_by fuel _ => fuel
decreasing_by omega

/-- Under the accepted degree band and an input/control envelope W, every Nat
register in every reachable reducer activation is bounded by the explicit
parameter-width exponent. -/
theorem rawReduceFuelActivationTrace_registers_lt
    {modulus degree fuel a W : Nat}
    (hmodLower : 2 ^ degree ≤ modulus)
    (hmodUpper : modulus < 2 ^ (degree + 1))
    (hdegree : degree < W) (hW : 0 < W)
    (hfuel : fuel ≤ W) (ha : a < 2 ^ W) :
    ∀ frame ∈ rawReduceFuelActivationTrace modulus degree fuel a,
      ∀ word ∈ frame.registers,
        word < 2 ^ rawArithmeticParameterWidth W := by
  have hdegreePlus : degree + 1 ≤ W := by omega
  have hmodWidth : modulus < 2 ^ W :=
    lt_of_lt_of_le hmodUpper
      (Nat.pow_le_pow_right (by decide : 0 < 2) hdegreePlus)
  induction fuel generalizing a with
  | zero =>
      intro frame hframe word hword
      simp only [rawReduceFuelActivationTrace, List.mem_singleton] at hframe
      subst frame
      simp [rawArithmeticReduceFrame] at hword
      rcases hword with hword | hword | hword | hword | hword | hword
      · subst word
        exact rawArithmetic_width_lt_parameter hmodWidth
      · subst word
        exact rawArithmetic_le_pow_parameter (Nat.le_of_lt hdegree)
      · subst word
        exact rawArithmetic_le_pow_parameter (by omega)
      · subst word
        exact rawArithmetic_width_lt_parameter ha
      · subst word
        positivity
      · subst word
        exact rawArithmetic_width_lt_parameter ha
  | succ fuel ih =>
      by_cases hsmall : a < 2 ^ degree
      · intro frame hframe word hword
        simp only [rawReduceFuelActivationTrace, if_pos hsmall,
          List.mem_singleton] at hframe
        subst frame
        simp [rawArithmeticReduceFrame] at hword
        rcases hword with hword | hword | hword | hword | hword | hword
        · subst word
          exact rawArithmetic_width_lt_parameter hmodWidth
        · subst word
          exact rawArithmetic_le_pow_parameter (Nat.le_of_lt hdegree)
        · subst word
          exact rawArithmetic_le_pow_parameter (by omega)
        · subst word
          exact rawArithmetic_width_lt_parameter ha
        · subst word
          positivity
        · subst word
          exact rawArithmetic_width_lt_parameter ha
      · have hcurrentLower : 2 ^ degree ≤ a := Nat.le_of_not_gt hsmall
        have hlog : Nat.log2 a < W := rawLog2_lt_of_lt_pow hW ha
        have hdegreeLe : degree ≤ Nat.log2 a := by
          have hpow : degree < Nat.log2 a + 1 :=
            (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).1
              (lt_of_le_of_lt hcurrentLower (Nat.lt_log2_self (n := a)))
          omega
        let power := 2 ^ (Nat.log2 a - degree)
        let shifted := modulus * power
        let step := rawReduceStepBitCosted modulus degree a
        have hshifted : shifted < 2 ^ W := by
          dsimp [shifted, power]
          have hmul := Nat.mul_lt_mul_of_pos_right hmodUpper
            (by positivity : 0 < 2 ^ (Nat.log2 a - degree))
          have hexp : degree + 1 + (Nat.log2 a - degree) = Nat.log2 a + 1 := by omega
          have hscaled : modulus * 2 ^ (Nat.log2 a - degree) <
              2 ^ (Nat.log2 a + 1) := by
            calc
              _ < 2 ^ (degree + 1) * 2 ^ (Nat.log2 a - degree) := hmul
              _ = 2 ^ (Nat.log2 a + 1) := by rw [← pow_add, hexp]
          have hexpBound : Nat.log2 a + 1 ≤ W := by omega
          exact lt_of_lt_of_le hscaled
            (Nat.pow_le_pow_right (by decide : 0 < 2) hexpBound)
        have hstep : step.1 < 2 ^ W := by
          dsimp [step]
          rw [rawReduceStepBitCosted_fst]
          have hstepLog := rawReduceStep_lt_pow_of_modulus_band
            degree modulus a hmodLower hmodUpper hcurrentLower
          exact lt_of_lt_of_le hstepLog
            (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_lt hlog))
        have hframeWidth : ∀ word ∈
            (rawArithmeticReduceFrame modulus degree (fuel + 1) a shifted step.1).registers,
            word < 2 ^ rawArithmeticParameterWidth W := by
          intro word hword
          simp [rawArithmeticReduceFrame] at hword
          rcases hword with hword | hword | hword | hword | hword | hword
          · subst word
            exact rawArithmetic_width_lt_parameter hmodWidth
          · subst word
            exact rawArithmetic_le_pow_parameter (Nat.le_of_lt hdegree)
          · subst word
            exact rawArithmetic_le_pow_parameter (by omega)
          · subst word
            exact rawArithmetic_width_lt_parameter ha
          · subst word
            exact rawArithmetic_width_lt_parameter hshifted
          · subst word
            exact rawArithmetic_width_lt_parameter hstep
        intro frame hframes word hword
        simp only [rawReduceFuelActivationTrace, if_neg hsmall,
          List.mem_cons] at hframes
        rcases hframes with hhead | htail
        · subst frame
          exact hframeWidth word hword
        · exact ih (by omega) hstep frame htail word hword

/-- A reduction trace has at most one frame per fuel level, including its
terminal test frame when fuel is nonzero. -/
theorem rawReduceFuelActivationTrace_length_le
    (modulus degree fuel a : Nat) :
    (rawReduceFuelActivationTrace modulus degree fuel a).length ≤ fuel + 1 := by
  induction fuel generalizing a with
  | zero => simp [rawReduceFuelActivationTrace]
  | succ fuel ih =>
      by_cases hsmall : a < 2 ^ degree
      · simp [rawReduceFuelActivationTrace, hsmall]
      · simp only [rawReduceFuelActivationTrace, if_neg hsmall,
          List.length_cons]
        have htail := ih (rawReduceStepBitCosted modulus degree a).1
        omega

end CorruptedFieldRecovery
