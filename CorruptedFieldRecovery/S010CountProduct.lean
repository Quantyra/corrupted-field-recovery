import Mathlib.Tactic
import CorruptedFieldRecovery.S010ProductBounds

namespace CorruptedFieldRecovery

theorem four_nat_sub_factors_normalized_lower
    {A b₁ b₂ b₃ b₄ : Nat}
    (hA : 0 < A)
    (hb₁ : b₁ ≤ A) (hb₂ : b₂ ≤ A) (hb₃ : b₃ ≤ A) (hb₄ : b₄ ≤ A)
    (hloss : (b₁ : ℚ) / A + (b₂ : ℚ) / A +
      (b₃ : ℚ) / A + (b₄ : ℚ) / A ≤ 1) :
    ((A - b₁ : Nat) : ℚ) / A * (((A - b₂ : Nat) : ℚ) / A) *
      (((A - b₃ : Nat) : ℚ) / A) * (((A - b₄ : Nat) : ℚ) / A) ≥
        1 - ((b₁ : ℚ) / A + (b₂ : ℚ) / A +
          (b₃ : ℚ) / A + (b₄ : ℚ) / A) := by
  have hAq : (0 : ℚ) < A := by exact_mod_cast hA
  have h₁ : ((A - b₁ : Nat) : ℚ) / A = 1 - (b₁ : ℚ) / A := by
    rw [Nat.cast_sub hb₁]
    field_simp
  have h₂ : ((A - b₂ : Nat) : ℚ) / A = 1 - (b₂ : ℚ) / A := by
    rw [Nat.cast_sub hb₂]
    field_simp
  have h₃ : ((A - b₃ : Nat) : ℚ) / A = 1 - (b₃ : ℚ) / A := by
    rw [Nat.cast_sub hb₃]
    field_simp
  have h₄ : ((A - b₄ : Nat) : ℚ) / A = 1 - (b₄ : ℚ) / A := by
    rw [Nat.cast_sub hb₄]
    field_simp
  rw [h₁, h₂, h₃, h₄]
  apply four_one_sub_product_lower
  · positivity
  · positivity
  · positivity
  · positivity
  · exact hloss

end CorruptedFieldRecovery
