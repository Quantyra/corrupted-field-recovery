import CorruptedFieldRecovery.RawPolyMulBounds

/-! A bit-operation cost semantics for carryless Nat-mask multiplication.
Each active recursive level charges the bit widths of the divider and
remainder operations, conditional selection, doubling shift, and XOR. This is
an explicit word-bit model for the actual recursive multiplier; it is not a
claim about a particular Lean compiler or machine runtime. -/

namespace CorruptedFieldRecovery

/-- Width of the unsigned binary representation, with zero charged one bit. -/
def rawNatBitWidth (n : Nat) : Nat := Nat.log2 n + 1

/-- Instrumented execution of the existing carryless multiplier. The first
component is definitionally computed by the same Nat recurrence; the second
accumulates the declared bit charges for that recurrence. -/
def rawPolyMulBitCosted (a : Nat) : Nat → Nat × Nat
  | 0 => (0, rawNatBitWidth 0)
  | b + 1 =>
      let child := rawPolyMulBitCosted a ((b + 1) / 2)
      let low := if (b + 1) % 2 = 1 then a else 0
      let shifted := 2 * child.1
      (Nat.xor low shifted,
        child.2 + 1 + 4 * rawNatBitWidth (b + 1) +
          rawNatBitWidth a + rawNatBitWidth child.1 + rawNatBitWidth shifted)
termination_by b => b
decreasing_by
  exact Nat.div_lt_self (by omega) (by decide)

private theorem rawNatBitWidth_le_of_lt_pow {n k : Nat}
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

/-- The instrumented result is exactly the executable carryless product. -/
theorem rawPolyMulBitCosted_fst (a b : Nat) :
    (rawPolyMulBitCosted a b).1 = rawPolyMul a b := by
  induction b using Nat.strong_induction_on with
  | h b ih =>
      cases b with
      | zero => simp [rawPolyMulBitCosted, rawPolyMul]
      | succ b =>
          have hdiv : (b + 1) / 2 < b + 1 := Nat.div_lt_self (Nat.succ_pos b) (by decide)
          rw [rawPolyMulBitCosted]
          rw [rawPolyMul, if_neg (Nat.succ_ne_zero b)]
          rw [ih ((b + 1) / 2) hdiv]

/-- If the multiplier has at most `k` bits and the multiplicand at most `r`
bits, the costed execution uses at most `8 (r+k+2)(k+1)` bit operations in
the declared model. The quadratic bound follows from at most one recursive
level per multiplier bit, with linear-width primitive charges at each level. -/
theorem rawPolyMulBitCosted_cost_le {r k a b : Nat}
    (ha : a < 2 ^ r) (hb : b < 2 ^ k) :
    (rawPolyMulBitCosted a b).2 ≤ 8 * (r + k + 2) * (k + 1) := by
  induction k generalizing a b with
  | zero =>
      have hb0 : b = 0 := by omega
      subst b
      simp [rawPolyMulBitCosted, rawNatBitWidth]
      omega
  | succ k ih =>
      cases b with
      | zero =>
          simp [rawPolyMulBitCosted, rawNatBitWidth]
          have hA : 1 ≤ r + k + 3 := by omega
          have hB : 1 ≤ k + 2 := by omega
          have hprod := Nat.mul_le_mul hA hB
          have hscaled := Nat.mul_le_mul_left 8 hprod
          simpa [Nat.mul_assoc, Nat.add_assoc] using
            le_trans (by decide : 1 ≤ 8) hscaled
      | succ b =>
          have hb' : b + 1 < 2 ^ (k + 1) := by simpa using hb
          have hhalf : (b + 1) / 2 < 2 ^ k := by
            apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).2
            simpa [pow_succ, Nat.mul_comm] using hb'
          have hchildCost := ih ha hhalf
          have hchildProduct := rawPolyMul_lt_pow r k a ((b + 1) / 2) ha hhalf
          have hchild : (rawPolyMulBitCosted a ((b + 1) / 2)).1 < 2 ^ (r + k) := by
            rw [rawPolyMulBitCosted_fst]
            exact hchildProduct
          have hshifted : 2 * (rawPolyMulBitCosted a ((b + 1) / 2)).1 <
              2 ^ (r + k + 1) := by
            calc
              2 * (rawPolyMulBitCosted a ((b + 1) / 2)).1 < 2 * 2 ^ (r + k) :=
                Nat.mul_lt_mul_of_pos_left hchild (by decide)
              _ = 2 ^ (r + k + 1) := by rw [pow_succ]; ring
          have hchildWidth : rawNatBitWidth
              (rawPolyMulBitCosted a ((b + 1) / 2)).1 ≤ r + k + 1 :=
            rawNatBitWidth_le_of_lt_pow hchild
          have hshiftedWidth : rawNatBitWidth
              (2 * (rawPolyMulBitCosted a ((b + 1) / 2)).1) ≤ r + k + 2 :=
            rawNatBitWidth_le_of_lt_pow hshifted
          have hbwidth : rawNatBitWidth (b + 1) ≤ k + 2 :=
            rawNatBitWidth_le_of_lt_pow hb'
          have hawidth : rawNatBitWidth a ≤ r + 1 :=
            rawNatBitWidth_le_of_lt_pow ha
          have hcost :
              (rawPolyMulBitCosted a ((b + 1) / 2)).2 + 1 +
                  4 * rawNatBitWidth (b + 1) + rawNatBitWidth a +
                  rawNatBitWidth (rawPolyMulBitCosted a ((b + 1) / 2)).1 +
                  rawNatBitWidth (2 * (rawPolyMulBitCosted a ((b + 1) / 2)).1) ≤
                8 * (r + k + 3) * (k + 2) := by
            have hstep : 1 + 4 * (k + 2) + (r + 1) + (r + k + 1) +
                (r + k + 2) ≤ 8 * (r + k + 3) := by omega
            have hcharge : 1 + 4 * rawNatBitWidth (b + 1) + rawNatBitWidth a +
                rawNatBitWidth (rawPolyMulBitCosted a ((b + 1) / 2)).1 +
                rawNatBitWidth (2 * (rawPolyMulBitCosted a ((b + 1) / 2)).1) ≤
              1 + 4 * (k + 2) + (r + 1) + (r + k + 1) + (r + k + 2) := by
              omega
            calc
              _ ≤ 8 * (r + k + 2) * (k + 1) +
                  (1 + 4 * (k + 2) + (r + 1) + (r + k + 1) + (r + k + 2)) := by
                    nlinarith [hchildCost, hcharge]
              _ ≤ 8 * (r + k + 2) * (k + 1) + 8 * (r + k + 3) := by
                    nlinarith [hstep]
              _ ≤ 8 * (r + k + 3) * (k + 2) := by
                    ring_nf
                    omega
          simpa only [rawPolyMulBitCosted] using hcost

end CorruptedFieldRecovery
