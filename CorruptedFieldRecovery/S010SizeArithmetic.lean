import Mathlib.Tactic

namespace CorruptedFieldRecovery

theorem scaled_tau_lt_field_size {s R tau : Nat}
    (hs : 2 * R + 5 ≤ s)
    (htau : tau < 2 ^ (s / 2 + 1)) :
    4 * (2 ^ R * tau) < 2 ^ s := by
  have hmul : 2 ^ R * tau < 2 ^ (R + (s / 2 + 1)) := by
    calc
      2 ^ R * tau < 2 ^ R * 2 ^ (s / 2 + 1) :=
        (Nat.mul_lt_mul_left (by positivity : 0 < 2 ^ R)).2 htau
      _ = 2 ^ (R + (s / 2 + 1)) := by rw [← Nat.pow_add]
  have hexp : R + (s / 2 + 1) + 2 ≤ s := by omega
  have hpow : 2 ^ (R + (s / 2 + 1) + 2) ≤ 2 ^ s :=
    Nat.pow_le_pow_right (by decide : 1 ≤ 2) hexp
  calc
    4 * (2 ^ R * tau) = 2 ^ 2 * (2 ^ R * tau) := by norm_num
    _ < 2 ^ 2 * 2 ^ (R + (s / 2 + 1)) :=
      (Nat.mul_lt_mul_left (by norm_num : 0 < 2 ^ 2)).2 hmul
    _ = 2 ^ (R + (s / 2 + 1) + 2) := by
      rw [← Nat.pow_add]
      congr 1
      omega
    _ ≤ 2 ^ s := hpow

theorem scaled_support_lt_field_size {s R : Nat}
    (hs : 2 * R + 5 ≤ s) :
    32 * 2 ^ (2 * R) ≤ 2 ^ s := by
  have hexp : 5 + 2 * R ≤ s := by omega
  have hpow : 2 ^ (5 + 2 * R) ≤ 2 ^ s :=
    Nat.pow_le_pow_right (by decide : 1 ≤ 2) hexp
  calc
    32 * 2 ^ (2 * R) = 2 ^ (5 + 2 * R) := by norm_num [Nat.pow_add]
    _ ≤ 2 ^ s := hpow

end CorruptedFieldRecovery
