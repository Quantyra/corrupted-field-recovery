import CorruptedFieldRecovery.RawArithmeticReduceTraceWidth
import CorruptedFieldRecovery.RawRabinGcdCorrectness

/-! Reachable activation snapshots for the costed Nat-mask Euclidean GCD.
The trace follows the exact remainder recursion and records the returned child
value. Width bounds are conditional input-register facts, not runtime claims. -/

namespace CorruptedFieldRecovery

private theorem rawGcd_width_lt_parameter {n W : Nat} (hn : n < 2 ^ W) :
    n < 2 ^ rawArithmeticParameterWidth W := by
  have hle : W ≤ rawArithmeticParameterWidth W := by
    unfold rawArithmeticParameterWidth
    omega
  exact lt_of_lt_of_le hn
    (Nat.pow_le_pow_right (by decide : 0 < 2) hle)

/-- A GCD activation snapshot containing both inputs, the computed remainder,
and the returned recursive value. -/
def rawArithmeticGcdActivationFrame
    (a b remainder output : Nat) : RawArithmeticFrame :=
  ⟨.gcd, [a, b, remainder, output], by simp⟩

/-- Activation path of the exact costed Euclidean recursion. -/
def rawPolynomialGcdActivationTrace : Nat → Nat → List RawArithmeticFrame
  | a, 0 => [rawArithmeticGcdActivationFrame a 0 0 a]
  | a, 1 => [rawArithmeticGcdActivationFrame a 1 0 1]
  | a, b + 2 =>
      let rem := rawPolynomialRemainderBitCosted a (b + 2)
      let rest := rawPolynomialGcdBitCosted (b + 2) rem.1
      rawArithmeticGcdActivationFrame a (b + 2) rem.1 rest.1 ::
        rawPolynomialGcdActivationTrace (b + 2) rem.1
termination_by _ b => b
decreasing_by
  rw [rawPolynomialRemainderBitCosted_fst]
  exact rawPolynomialRemainder_lt (by omega)

private theorem rawPolynomialGcdBitCosted_value_lt_pow
    {a b W : Nat} (hW : 0 < W) (ha : a < 2 ^ W) (hb : b < 2 ^ W) :
    (rawPolynomialGcdBitCosted a b).1 < 2 ^ W := by
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
      cases b with
      | zero => simpa [rawPolynomialGcdBitCosted] using ha
      | succ b =>
          cases b with
          | zero =>
              have hone : 1 < 2 ^ W := by
                have hpow : 2 ≤ 2 ^ W := by
                  calc
                    2 = 2 ^ 1 := by norm_num
                    _ ≤ 2 ^ W := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
                omega
              simpa [rawPolynomialGcdBitCosted] using hone
          | succ b =>
              let rem := rawPolynomialRemainderBitCosted a (b + 2)
              have hrem : rem.1 < b + 2 := by
                rw [rawPolynomialRemainderBitCosted_fst]
                exact rawPolynomialRemainder_lt (by omega)
              have hremWidth : rem.1 < 2 ^ W := lt_trans hrem hb
              have hchild := ih rem.1 hrem (a := b + 2) hb hremWidth
              simpa [rawPolynomialGcdBitCosted, rem] using hchild

/-- Every saved register on the reachable Euclidean recursion path fits the
same W-bit envelope as its two initial inputs. -/
theorem rawPolynomialGcdActivationTrace_registers_lt
    {a b W : Nat} (hW : 0 < W)
    (ha : a < 2 ^ W) (hb : b < 2 ^ W) :
    ∀ frame ∈ rawPolynomialGcdActivationTrace a b,
      ∀ word ∈ frame.registers,
        word < 2 ^ rawArithmeticParameterWidth W := by
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
      cases b with
      | zero =>
          intro frame hframe word hword
          simp only [rawPolynomialGcdActivationTrace, List.mem_singleton] at hframe
          subst frame
          simp [rawArithmeticGcdActivationFrame] at hword
          rcases hword with hword_a | hword_zero | hword_a_again
          · rw [hword_a]
            exact rawGcd_width_lt_parameter ha
          · rw [hword_zero]
            exact Nat.pow_pos (by decide : 0 < (2 : Nat))
          · rw [hword_a_again]
            exact rawGcd_width_lt_parameter ha
      | succ b =>
          cases b with
          | zero =>
              intro frame hframe word hword
              simp only [Nat.zero_add, rawPolynomialGcdActivationTrace,
                List.mem_singleton] at hframe
              subst frame
              simp [rawArithmeticGcdActivationFrame] at hword
              rcases hword with hword_a | hword_zero | hword_one
              · rw [hword_a]
                exact rawGcd_width_lt_parameter ha
              · rw [hword_zero]
                exact rawGcd_width_lt_parameter hb
              · rcases hword_one with hword_zero | hword_one
                · rw [hword_zero]
                  exact Nat.pow_pos (by decide : 0 < (2 : Nat))
                · rw [hword_one]
                  exact rawGcd_width_lt_parameter hb
          | succ b =>
              let rem := rawPolynomialRemainderBitCosted a (b + 2)
              let rest := rawPolynomialGcdBitCosted (b + 2) rem.1
              have hrem : rem.1 < b + 2 := by
                rw [rawPolynomialRemainderBitCosted_fst]
                exact rawPolynomialRemainder_lt (by omega)
              have hremWidth : rem.1 < 2 ^ W := lt_trans hrem hb
              have houtput : rest.1 < 2 ^ W := by
                dsimp [rest]
                exact rawPolynomialGcdBitCosted_value_lt_pow hW hb hremWidth
              have hparent : ∀ word ∈
                  (rawArithmeticGcdActivationFrame a (b + 2) rem.1 rest.1).registers,
                  word < 2 ^ rawArithmeticParameterWidth W := by
                intro word hword
                simp [rawArithmeticGcdActivationFrame] at hword
                rcases hword with hword | hword | hword | hword
                · subst word
                  exact rawGcd_width_lt_parameter ha
                · subst word
                  exact rawGcd_width_lt_parameter hb
                · subst word
                  exact rawGcd_width_lt_parameter hremWidth
                · subst word
                  exact rawGcd_width_lt_parameter houtput
              intro frame hframes word hword
              simp only [rawPolynomialGcdActivationTrace, List.mem_cons] at hframes
              rcases hframes with hhead | htail
              · subst frame
                exact hparent word hword
              · exact ih rem.1 hrem (a := b + 2) hb hremWidth frame htail word hword

/-- The activation trace length is bounded by the corresponding GCD charge. -/
theorem rawPolynomialGcdActivationTrace_length_le_charge (a b : Nat) :
    (rawPolynomialGcdActivationTrace a b).length ≤
      (rawPolynomialGcdBitCosted a b).2 := by
  have htrace : ∀ k x, (rawPolynomialGcdActivationTrace x k).length ≤
      rawPolynomialGcdBitCostedFrames x k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro x
        cases k with
        | zero => simp [rawPolynomialGcdActivationTrace,
            rawPolynomialGcdBitCostedFrames]
        | succ k =>
            cases k with
            | zero => simp [rawPolynomialGcdActivationTrace,
                rawPolynomialGcdBitCostedFrames]
            | succ k =>
                let rem := rawPolynomialRemainderBitCosted x (k + 2)
                have hrem : rem.1 < k + 2 := by
                  rw [rawPolynomialRemainderBitCosted_fst]
                  exact rawPolynomialRemainder_lt (by omega)
                have hchild := ih rem.1 hrem (k + 2)
                simp only [rawPolynomialGcdActivationTrace, List.length_cons,
                  rawPolynomialGcdBitCostedFrames]
                dsimp [rem] at hchild
                omega
  exact le_trans (htrace b a) (rawPolynomialGcdBitCostedFrames_le_charge a b)

end CorruptedFieldRecovery
