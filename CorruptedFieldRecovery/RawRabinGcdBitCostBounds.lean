import CorruptedFieldRecovery.RawRabinGcdBitCost

/-! A logarithmic-depth envelope for the declared charge of the actual
Euclidean recursion used by the raw Rabin gate. -/

namespace CorruptedFieldRecovery

private theorem rawRabinBitWidth_le_of_lt_pow {n k : Nat}
    (hn : n < 2 ^ k) : rawNatBitWidth n ≤ k + 1 := by
  unfold rawNatBitWidth
  by_cases hn0 : n = 0
  · simp [hn0]
  · have hk : 0 < k := by
      cases k with
      | zero => simp at hn; omega
      | succ k => omega
    have hlog := rawLog2_lt_of_lt_pow hk hn
    omega

private theorem rawRabin_lt_pow_of_log_lt {n k : Nat}
    (h : Nat.log2 n < k) : n < 2 ^ k := by
  by_cases hn0 : n = 0
  · simp [hn0]
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    have hlog : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
    have hp : 2 ^ (Nat.log2 n + 1) ≤ 2 ^ k := by
      exact Nat.pow_le_pow_right (by decide : 0 < 2)
        (Nat.succ_le_of_lt h)
    exact lt_of_lt_of_le hlog hp

/-- The exact costed Euclidean recursion has logarithmic depth. Under a common
`A`-bit envelope for its two inputs, its declared charge is bounded by a
polynomial in `A` times `log₂(divisor)+2`. This is a theorem about the explicit
charge recurrence, not a claim about Lean's machine execution time. -/
theorem rawPolynomialGcdBitCosted_cost_le {a b A : Nat}
    (hA : 0 < A) (ha : a < 2 ^ A) (hb : b < 2 ^ A) :
    (rawPolynomialGcdBitCosted a b).2 ≤
      (Nat.log2 b + 2) * (40 * (3 * A + 6) ^ 2 * (A + 1)) := by
  have hmain : ∀ k x y, Nat.log2 y = k → ∀ width,
      0 < width → x < 2 ^ width → y < 2 ^ width →
      (rawPolynomialGcdBitCosted x y).2 ≤
        (Nat.log2 y + 2) * (40 * (3 * width + 6) ^ 2 * (width + 1)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro x y hylog width hw hx hy
      have hPpos : 1 ≤ 40 * (3 * width + 6) ^ 2 * (width + 1) := by
        nlinarith [hw]
      by_cases hy0 : y = 0
      · simp [rawPolynomialGcdBitCosted, hy0, rawNatBitWidth]
        nlinarith [hPpos]
      · by_cases hy1 : y = 1
        · simp [rawPolynomialGcdBitCosted, hy1, rawNatBitWidth]
          nlinarith [hPpos]
        · have hytwo : 1 < y := by omega
          obtain ⟨d, hydecomp⟩ : ∃ d, y = d + 2 :=
            ⟨y - 2, by omega⟩
          subst y
          have hlogyWidth : Nat.log2 (d + 2) < width :=
            rawLog2_lt_of_lt_pow hw hy
          let rem := rawPolynomialRemainderBitCosted x (d + 2)
          have hrem : rem.1 < 2 ^ Nat.log2 (d + 2) := by
            rw [show rem.1 = rawPolynomialRemainder x (d + 2) by
              dsimp [rem]
              exact rawPolynomialRemainderBitCosted_fst x (d + 2)]
            exact rawPolynomialRemainder_lt_pow_log hytwo
          have hs : 0 < Nat.log2 (d + 2) := by
            by_contra h
            have hz : Nat.log2 (d + 2) = 0 := by omega
            have hupp : d + 2 < 2 ^ (Nat.log2 (d + 2) + 1) :=
              Nat.lt_log2_self
            rw [hz] at hupp
            omega
          have hremLog : Nat.log2 rem.1 < Nat.log2 (d + 2) :=
            rawLog2_lt_of_lt_pow hs hrem
          rw [hylog] at hremLog
          have hlogyK : k < width := by simpa [hylog] using hlogyWidth
          have hremWidth : rem.1 < 2 ^ width := by
            apply rawRabin_lt_pow_of_log_lt
            exact lt_of_lt_of_le hremLog (Nat.le_of_lt hlogyK)
          have hremCost := rawPolynomialRemainderBitCosted_cost_le
            hw hx hytwo
          have hwidthY : rawNatBitWidth (d + 2) ≤ width := by
            unfold rawNatBitWidth
            omega
          have hwidthLog :
              rawNatBitWidth (Nat.log2 (d + 2)) ≤ width := by
            have hloglog : Nat.log2 (Nat.log2 (d + 2)) ≤ Nat.log2 (d + 2) :=
              Nat.log2_le_self _
            unfold rawNatBitWidth
            omega
          have hlocal : rawNatBitWidth (d + 2) + rem.2 ≤
              40 * (3 * width + 6) ^ 2 * (width + 1) := by
            have hterm : width + Nat.log2 (d + 2) +
                rawNatBitWidth (Nat.log2 (d + 2)) + 4 ≤ 3 * width + 6 := by
              omega
            have hquad : 40 * (width + Nat.log2 (d + 2) +
                rawNatBitWidth (Nat.log2 (d + 2)) + 4) ^ 2 ≤
                40 * (3 * width + 6) ^ 2 := by
              gcongr
            have hremCost' : rem.2 ≤
                width * (40 * (width + Nat.log2 (d + 2) +
                  rawNatBitWidth (Nat.log2 (d + 2)) + 4) ^ 2) := by
              simpa [rem] using hremCost
            have hcost : rem.2 ≤ width * (40 * (3 * width + 6) ^ 2) := by
              exact le_trans hremCost'
                (Nat.mul_le_mul_left width hquad)
            have hfactor : width + width * (40 * (3 * width + 6) ^ 2) ≤
                40 * (3 * width + 6) ^ 2 * (width + 1) := by
              nlinarith [hw]
            calc
              _ ≤ width + width * (40 * (3 * width + 6) ^ 2) := by
                exact Nat.add_le_add hwidthY hcost
              _ ≤ 40 * (3 * width + 6) ^ 2 * (width + 1) := hfactor
          have hrest := ih (Nat.log2 rem.1) hremLog (d + 2) rem.1 rfl
            width hw hy hremWidth
          have hrec : (rawPolynomialGcdBitCosted (d + 2) rem.1).2 ≤
              (Nat.log2 rem.1 + 2) *
                (40 * (3 * width + 6) ^ 2 * (width + 1)) := hrest
          simp only [rawPolynomialGcdBitCosted]
          have hdepth : Nat.log2 rem.1 + 2 ≤ Nat.log2 (d + 2) + 1 := by omega
          have hdepthMul := Nat.mul_le_mul_right
            (40 * (3 * width + 6) ^ 2 * (width + 1)) hdepth
          calc
            _ ≤ (40 * (3 * width + 6) ^ 2 * (width + 1)) +
                (Nat.log2 rem.1 + 2) *
                  (40 * (3 * width + 6) ^ 2 * (width + 1)) := by
                    exact Nat.add_le_add hlocal hrec
            _ ≤ (Nat.log2 (d + 2) + 2) *
                  (40 * (3 * width + 6) ^ 2 * (width + 1)) := by
                    nlinarith [hdepthMul]
  exact hmain (Nat.log2 b) a b rfl A hA ha hb

end CorruptedFieldRecovery
