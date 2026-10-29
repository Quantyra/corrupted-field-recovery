import CorruptedFieldRecovery.ProperSubfieldCounts
import Mathlib.Tactic

namespace CorruptedFieldRecovery

private theorem sum_pow_two_range_succ (m : Nat) :
    (∑ d ∈ Finset.range (m + 1), 2 ^ d) = 2 ^ (m + 1) - 1 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, Nat.pow_succ]
      omega

theorem proper_degree_sum_lt_half_power
    (K : Type*) [Field K] [Finite K] [Algebra BinaryField K]
    [FiniteDimensional BinaryField K] (s : Nat)
    (hs : Module.finrank BinaryField K = s) :
    (∑ d ∈ properDegrees K, 2 ^ d) < 2 ^ (s / 2 + 1) := by
  classical
  let m := s / 2
  have hsubset : properDegrees K ⊆ Finset.range (m + 1) := by
    intro d hd
    simp only [properDegrees, Finset.mem_filter, Finset.mem_range] at hd
    rcases hd with ⟨hdlt, hdiv⟩
    have hds : d < s := by simpa [hs] using hdlt
    have hdpos : 0 < s := by rw [← hs]; exact Module.finrank_pos
    have hdivs : d ∣ s := by simpa [hs] using hdiv
    have hdle : d ≤ s := Nat.le_of_dvd hdpos hdivs
    by_cases hdz : d = 0
    · simp [m, hdz]
    · have hdpos' : 0 < d := Nat.pos_of_ne_zero hdz
      obtain ⟨k, hk⟩ := hdivs
      have hkpos : 0 < k := by
        by_contra h
        have : k = 0 := by omega
        simp [this] at hk
        omega
      have hkne : k ≠ 1 := by
        intro heq
        subst k
        simp at hk
        omega
      have hkge : 2 ≤ k := by omega
      have hmul : d * 2 ≤ d * k := Nat.mul_le_mul_left d hkge
      have h2d : 2 * d ≤ s := by
        have hk' : s = d * k := by omega
        nlinarith [hmul]
      have hdivbound : d ≤ s / 2 := (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2 (by nlinarith)
      simp [m]
      omega
  have hsum : (∑ d ∈ properDegrees K, 2 ^ d) ≤
      ∑ d ∈ Finset.range (m + 1), 2 ^ d := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro d hd hnot
    positivity
  rw [sum_pow_two_range_succ] at hsum
  have hpos : 0 < 2 ^ (m + 1) := by positivity
  have hstrict : (∑ d ∈ properDegrees K, 2 ^ d) < 2 ^ (m + 1) := by omega
  simpa [m] using hstrict

end CorruptedFieldRecovery