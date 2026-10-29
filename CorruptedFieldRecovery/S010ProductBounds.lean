import Mathlib.Tactic

namespace CorruptedFieldRecovery

/-- Two independent retained fractions lose at most the sum of their losses. -/
theorem one_sub_mul_one_sub_lower {x y : ℚ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (1 - x) * (1 - y) ≥ 1 - (x + y) := by
  nlinarith [mul_nonneg hx hy]

/-- Four sequential good fractions have total loss at most the sum of the
four individual bad fractions. The sum bound ensures each factor being
multiplied is nonnegative. -/
theorem four_one_sub_product_lower {a b c d : ℚ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (habcd : a + b + c + d ≤ 1) :
    (1 - a) * (1 - b) * (1 - c) * (1 - d) ≥
      1 - (a + b + c + d) := by
  have hc1 : c ≤ 1 := by linarith
  have hd1 : d ≤ 1 := by linarith
  have h_ab := one_sub_mul_one_sub_lower ha hb
  have h_abc' : (1 - a) * (1 - b) * (1 - c) ≥ 1 - (a + b + c) := by
    have hpair := one_sub_mul_one_sub_lower (by linarith : 0 ≤ a + b) hc
    calc
      (1 - a) * (1 - b) * (1 - c) ≥ (1 - (a + b)) * (1 - c) := by
        have hmul := mul_nonneg (sub_nonneg.mpr h_ab) (by linarith : 0 ≤ 1 - c)
        nlinarith [hmul]
      _ ≥ 1 - (a + b + c) := hpair
  calc
    (1 - a) * (1 - b) * (1 - c) * (1 - d) ≥
        (1 - (a + b + c)) * (1 - d) := by
      have hmul := mul_nonneg (sub_nonneg.mpr h_abc') (by linarith : 0 ≤ 1 - d)
      nlinarith [hmul]
    _ ≥ 1 - (a + b + c + d) :=
      one_sub_mul_one_sub_lower (by linarith : 0 ≤ a + b + c) hd

end CorruptedFieldRecovery
