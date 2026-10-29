import Mathlib.Tactic

namespace CorruptedFieldRecovery

/-- The sequential clean-vector losses are bounded by beta once the clean
set has density at least 1/2^R in the hidden-field ambient space. `gain` is
q^3/|A|≤2^R; it avoids assuming that the clean set is K-linear. -/
theorem four_clean_losses_le_beta
    {q a p t : ℚ} (hq : 0 < q) (ha : 0 < a) (ht : 0 ≤ t)
    (hgain : q ^ 3 / a ≤ p) :
    1 / a + q / a + q ^ 2 / a + t * q ^ 2 / a ≤
      p / q ^ 3 + p / q ^ 2 + p / q + p * t / q := by
  have hq2 : 0 < q ^ 2 := by positivity
  have hq3 : 0 < q ^ 3 := by positivity
  have h1 : 1 / a ≤ p / q ^ 3 := by
    have hid : 1 / a = (q ^ 3 / a) / q ^ 3 := by field_simp
    rw [hid]
    exact div_le_div_of_nonneg_right hgain (by positivity)
  have h2id : q / a = (q ^ 3 / a) / q ^ 2 := by
    field_simp
  have h2 : q / a ≤ p / q ^ 2 := by
    rw [h2id]
    exact div_le_div_of_nonneg_right hgain (by positivity)
  have h3id : q ^ 2 / a = (q ^ 3 / a) / q := by
    field_simp
  have h3 : q ^ 2 / a ≤ p / q := by
    rw [h3id]
    exact div_le_div_of_nonneg_right hgain (by positivity)
  have h4id : t * q ^ 2 / a = t * (q ^ 3 / a) / q := by
    field_simp
  have h4 : t * q ^ 2 / a ≤ p * t / q := by
    rw [h4id]
    have hdiv : (q ^ 3 / a) / q ≤ p / q :=
      div_le_div_of_nonneg_right hgain (by positivity)
    calc
      t * (q ^ 3 / a) / q = t * ((q ^ 3 / a) / q) := by ring
      _ ≤ t * (p / q) := mul_le_mul_of_nonneg_left hdiv ht
      _ = p * t / q := by ring
  linarith

end CorruptedFieldRecovery
