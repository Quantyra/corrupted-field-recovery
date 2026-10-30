import CorruptedFieldRecovery.RawArithmeticRegisterSpaceModel

/-! Reachable multiplier activation snapshots and their width invariant.
This trace follows the exact recursive argument of `rawPolyMulBitCosted`; the
space statement is still the explicit register model, not Lean heap usage. -/

namespace CorruptedFieldRecovery

/-- The activation snapshots on the recursive path of the costed multiplier.
The saved child value and doubled value are included conservatively in each
frame's register set. -/
def rawPolyMulActivationTrace (a : Nat) : Nat → List RawArithmeticFrame
  | 0 => [rawArithmeticMultiplyFrame a 0 0 0]
  | b + 1 =>
      let child := rawPolyMulBitCosted a ((b + 1) / 2)
      let shifted := 2 * child.1
      rawArithmeticMultiplyFrame a (b + 1) child.1 shifted ::
        rawPolyMulActivationTrace a ((b + 1) / 2)
termination_by b => b
decreasing_by
  exact Nat.div_lt_self (by omega) (by decide)

/-- Every stored multiplier word on a reachable recursive path is bounded by
the product-width envelope `2W+1`, provided the original operands are W-bit. -/
theorem rawPolyMulActivationTrace_registers_lt
    {a b W : Nat} (ha : a < 2 ^ W) (hb : b < 2 ^ W) :
    ∀ frame ∈ rawPolyMulActivationTrace a b,
      ∀ word ∈ frame.registers, word < 2 ^ (2 * W + 1) := by
  induction b using Nat.strong_induction_on generalizing a W with
  | h b ih =>
      cases b with
      | zero =>
          intro frame hframe word hword
          simp only [rawPolyMulActivationTrace, List.mem_singleton] at hframe
          subst frame
          simp only [rawArithmeticMultiplyFrame, List.mem_cons] at hword
          rcases hword with hword | hword | hword | hword
          · subst word
            exact lt_trans ha (by
              apply Nat.pow_lt_pow_right (by decide : 1 < 2)
              omega)
          · subst word
            positivity
          · subst word
            positivity
          · rcases hword with hword | hfalse
            · subst word
              positivity
            · simp at hfalse
      | succ b =>
          have hchildIndex : (b + 1) / 2 < b + 1 :=
            Nat.div_lt_self (by omega) (by decide)
          have hhalf : (b + 1) / 2 < 2 ^ W := by
            exact lt_of_le_of_lt (Nat.div_le_self (b + 1) 2) hb
          let child := rawPolyMulBitCosted a ((b + 1) / 2)
          let shifted := 2 * child.1
          have hchildValue : child.1 < 2 ^ (W + W) := by
            dsimp [child]
            rw [rawPolyMulBitCosted_fst]
            exact rawPolyMul_lt_pow W W a ((b + 1) / 2) ha hhalf
          have hshifted : shifted < 2 ^ (W + W + 1) := by
            dsimp [shifted]
            calc
              2 * child.1 < 2 * 2 ^ (W + W) :=
                Nat.mul_lt_mul_of_pos_left hchildValue (by decide)
              _ = 2 ^ (W + W) * 2 := Nat.mul_comm _ _
              _ = 2 ^ (W + W + 1) := by rw [pow_succ]
          have hparent : ∀ word ∈
              (rawArithmeticMultiplyFrame a (b + 1) child.1 shifted).registers,
              word < 2 ^ (2 * W + 1) := by
            intro word hword
            simp only [rawArithmeticMultiplyFrame, List.mem_cons] at hword
            rcases hword with hword | hword | hword | hword
            · subst word
              exact lt_trans ha (by
                apply Nat.pow_lt_pow_right (by decide : 1 < 2)
                omega)
            · subst word
              exact lt_trans hb (by
                apply Nat.pow_lt_pow_right (by decide : 1 < 2)
                omega)
            · subst word
              exact lt_trans hchildValue (by
                apply Nat.pow_lt_pow_right (by decide : 1 < 2)
                omega)
            · rcases hword with hword | hfalse
              · subst word
                simpa [shifted, two_mul, Nat.add_assoc] using hshifted
              · simp at hfalse
          intro frame hframe word hword
          simp only [rawPolyMulActivationTrace, List.mem_cons] at hframe
          rcases hframe with hframe | hframe
          · subst frame
            exact hparent word hword
          · exact ih ((b + 1) / 2) hchildIndex ha hhalf frame hframe word hword

/-- The recursive multiplier trace has exactly `logarithmic recursion depth`
frames bounded by the multiplier-bit charge. -/
theorem rawPolyMulActivationTrace_length_le_charge (a b : Nat) :
    (rawPolyMulActivationTrace a b).length ≤
      (rawPolyMulBitCosted a b).2 := by
  induction b using Nat.strong_induction_on with
  | h b ih =>
      cases b with
      | zero => simp [rawPolyMulActivationTrace, rawPolyMulBitCosted, rawNatBitWidth]
      | succ b =>
          have hdiv : (b + 1) / 2 < b + 1 := Nat.div_lt_self (by omega) (by decide)
          have hchild := ih ((b + 1) / 2) hdiv
          simp only [rawPolyMulActivationTrace, List.length_cons,
            rawPolyMulBitCosted]
          omega

end CorruptedFieldRecovery
