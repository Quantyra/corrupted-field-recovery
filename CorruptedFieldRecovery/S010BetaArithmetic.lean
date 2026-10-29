import Mathlib.Tactic

namespace CorruptedFieldRecovery

theorem beta_span_terms_lt_sixteenth {p q : ℚ}
    (hq32 : 32 ≤ q) (hpq : 32 * p ≤ q) :
    p / q + p / q ^ 2 + p / q ^ 3 < 1 / 16 := by
  have hq : 0 < q := by linarith
  have hrecip : 1 / q ≤ 1 / 32 :=
    one_div_le_one_div_of_le (by norm_num) hq32
  have hfirst : p / q ≤ 1 / 32 := by
    rw [div_le_iff₀ hq]
    nlinarith [hpq]
  have hsecondid : p / q ^ 2 = (p / q) * (1 / q) := by
    field_simp
  have hsecond : p / q ^ 2 ≤ 1 / 1024 := by
    rw [hsecondid]
    calc
      (p / q) * (1 / q) ≤ (1 / 32) * (1 / 32) :=
        mul_le_mul hfirst hrecip (by positivity) (by norm_num)
      _ = 1 / 1024 := by norm_num
  have hthirdid : p / q ^ 3 = (p / q ^ 2) * (1 / q) := by
    field_simp
  have hthird : p / q ^ 3 ≤ 1 / 32768 := by
    rw [hthirdid]
    calc
      (p / q ^ 2) * (1 / q) ≤ (1 / 1024) * (1 / 32) :=
        mul_le_mul hsecond hrecip (by positivity) (by norm_num)
      _ = 1 / 32768 := by norm_num
  linarith

theorem beta_lt_half_from_size {s R T : Nat}
    (hsize : 2 * R + 5 ≤ s)
    (htau : 4 * (2 ^ R * T) < 2 ^ s) :
    ((2 ^ R : ℚ) * (1 + (2 ^ s : ℚ) + (2 ^ s : ℚ) ^ 2) /
      (2 ^ s : ℚ) ^ 3) +
      ((2 ^ R : ℚ) * T) / (2 ^ s : ℚ) < 1 / 2 := by
  let p : ℚ := 2 ^ R
  let q : ℚ := 2 ^ s
  have hq32Nat : 32 ≤ 2 ^ s := by
    have hs5 : 5 ≤ s := by omega
    have h := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hs5
    norm_num at h
    exact h
  have hpqNat : 32 * 2 ^ R ≤ 2 ^ s := by
    have hexp : R + 5 ≤ s := by omega
    have h := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hexp
    calc
      32 * 2 ^ R = 2 ^ R * 32 := by ring
      _ = 2 ^ (R + 5) := by norm_num [Nat.pow_add]
      _ ≤ 2 ^ s := h
  have hq32 : (32 : ℚ) ≤ q := by
    dsimp [q]
    exact_mod_cast hq32Nat
  have hpq : 32 * p ≤ q := by
    dsimp [p, q]
    exact_mod_cast hpqNat
  have hspan : p / q + p / q ^ 2 + p / q ^ 3 < 1 / 16 :=
    beta_span_terms_lt_sixteenth hq32 hpq
  have hqpos : 0 < q := by
    dsimp [q]
    positivity
  have htauQ : (4 : ℚ) * (p * T) < q := by
    dsimp [p, q]
    exact_mod_cast htau
  have htauFrac : (p * T) / q < 1 / 4 := by
    rw [div_lt_iff₀ hqpos]
    nlinarith [htauQ]
  have hrewrite :
      ((2 ^ R : ℚ) * (1 + (2 ^ s : ℚ) + (2 ^ s : ℚ) ^ 2) /
        (2 ^ s : ℚ) ^ 3) = p / q + p / q ^ 2 + p / q ^ 3 := by
    dsimp [p, q]
    field_simp
    ring
  have htauFrac' : ((2 ^ R : ℚ) * T) / (2 ^ s : ℚ) < 1 / 4 := by
    simpa [p, q] using htauFrac
  rw [hrewrite]
  linarith [hspan, htauFrac']

end CorruptedFieldRecovery