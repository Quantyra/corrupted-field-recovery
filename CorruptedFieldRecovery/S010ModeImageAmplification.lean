import CorruptedFieldRecovery.S010ConditionalAmplification
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic

namespace CorruptedFieldRecovery

noncomputable section

/-- Bernoulli's inequality gives the exact block estimate
`2 (C - 1)^C ≤ C^C` for every `C ≥ 2`. -/
theorem twice_sub_pow_le_pow (C : Nat) (hC : 2 ≤ C) :
    2 * (C - 1) ^ C ≤ C ^ C := by
  have hD : 0 < (C : ℚ) - 1 := by
    have hCrat : (1 : ℚ) < (C : ℚ) := by
      exact_mod_cast (show 1 < C by omega)
    linarith
  let x : ℚ := 1 / ((C : ℚ) - 1)
  have hx : 0 ≤ x := by positivity
  have hlin : 2 ≤ 1 + (C : ℚ) * x := by
    have hxC : 1 ≤ (C : ℚ) * x := by
      dsimp [x]
      field_simp [ne_of_gt hD]
      nlinarith
    linarith
  have hbern : 1 + (C : ℚ) * x ≤ (1 + x) ^ C :=
    one_add_le_pow_of_two_add_nonneg (by positivity) C
  have hratio : 2 ≤ ((C : ℚ) / ((C : ℚ) - 1)) ^ C := by
    have hid : 1 + x = (C : ℚ) / ((C : ℚ) - 1) := by
      dsimp [x]
      field_simp [ne_of_gt hD]
      ring
    rw [← hid]
    exact hlin.trans hbern
  have hrat : (2 : ℚ) * ((C : ℚ) - 1) ^ C ≤ (C : ℚ) ^ C := by
    have hden : 0 < ((C : ℚ) - 1) ^ C := pow_pos hD _
    have hratio' : 2 ≤ (C : ℚ) ^ C / ((C : ℚ) - 1) ^ C := by
      rw [← div_pow]
      exact hratio
    exact (le_div_iff₀ hden).mp hratio'
  have hcast : ((C - 1 : Nat) : ℚ) = (C : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ C)]
    simp
  rw [← hcast] at hrat
  exact_mod_cast hrat

/-- Repeating a one-trial event with probability at least `1/C` for `C*h`
independent trials yields the exact cross-multiplied `1 - 2⁻ʰ` amplification
bound. This is a finite counting statement; it does not identify an algorithm's
success predicate with `S`. -/
theorem repeatedSuccessSet_block_amplification
    {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (C h : Nat) (hC : 2 ≤ C)
    (htrial : C * S.card ≥ Fintype.card α) :
    2 ^ h * C ^ (C * h) * (repeatedSuccessSet S (C * h)).card ≥
      (2 ^ h - 1) * C ^ (C * h) * (Fintype.card α) ^ (C * h) := by
  let n := C * h
  have hbase := twice_sub_pow_le_pow C hC
  have hblock : 2 ^ h * (C - 1) ^ (C * h) ≤ C ^ (C * h) := by
    have hp := Nat.pow_le_pow_left hbase h
    calc
      2 ^ h * (C - 1) ^ (C * h) =
          (2 * (C - 1) ^ C) ^ h := by rw [pow_mul, Nat.mul_pow]
      _ ≤ (C ^ C) ^ h := hp
      _ = C ^ (C * h) := by rw [← pow_mul]
  have hamp := repeatedSuccessSet_amplification S C n (by omega) htrial
  have hstep :
      2 ^ h * (C ^ n - (C - 1) ^ n) ≥ (2 ^ h - 1) * C ^ n := by
    have hsub := Nat.sub_le_sub_left hblock (2 ^ h * C ^ n)
    calc
      2 ^ h * (C ^ n - (C - 1) ^ n) =
          2 ^ h * C ^ n - 2 ^ h * (C - 1) ^ n := Nat.mul_sub_left_distrib _ _ _
      _ ≥ 2 ^ h * C ^ n - C ^ n := hsub
      _ = (2 ^ h - 1) * C ^ n := by rw [Nat.sub_mul, one_mul]
  have hstepN :
      (2 ^ h - 1) * C ^ n * (Fintype.card α) ^ n ≤
        2 ^ h * (C ^ n - (C - 1) ^ n) * (Fintype.card α) ^ n :=
    Nat.mul_le_mul_right _ hstep
  have hmul := Nat.mul_le_mul_left (2 ^ h) hamp
  have hmul' :
      2 ^ h * (C ^ n - (C - 1) ^ n) * (Fintype.card α) ^ n ≤
        2 ^ h * C ^ n * (repeatedSuccessSet S n).card := by
    simpa only [Nat.mul_assoc] using hmul
  have hresult :
      (2 ^ h - 1) * C ^ n * (Fintype.card α) ^ n ≤
        2 ^ h * C ^ n * (repeatedSuccessSet S n).card := by
    calc
      _ ≤ 2 ^ h * (C ^ n - (C - 1) ^ n) * (Fintype.card α) ^ n := hstepN
      _ ≤ 2 ^ h * C ^ n * (repeatedSuccessSet S n).card := hmul'
  simpa [n, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hresult

/-- Conditional amplification for the actual mode-image event. As in the
one-trial theorem, `hgoodSuccess` is the explicit algorithmic implication
premise, not a result proved by the counting argument. -/
theorem modeImage_actual_success_amplification
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra BinaryField K] [FiniteDimensional BinaryField K] [Finite K]
    {s R r h : Nat} (hs : Module.finrank BinaryField K = s)
    (hsize : 2 * R + 5 ≤ s) (hrR : r ≤ R)
    (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K)
    (E : BinaryTensor (3 * s))
    (hr : Module.finrank BinaryField (modeImageSemanticSupport Q E) = r)
    (b : (Fin 4 → FieldTriple K) → Module.Basis (Fin s) BinaryField K)
    (Success : Finset (FiveWordTape s))
    (hgoodSuccess : actualFiveGoodTapeSet K Q
      (modeImageSemanticCleanFieldSet Q E) (modeImageSemanticSupport Q E) b ⊆ Success) :
    2 ^ h * (2 ^ (4 * R + 3)) ^ (2 ^ (4 * R + 3) * h) *
        (repeatedSuccessSet Success (2 ^ (4 * R + 3) * h)).card ≥
      (2 ^ h - 1) * (2 ^ (4 * R + 3)) ^ (2 ^ (4 * R + 3) * h) *
        (Fintype.card (FiveWordTape s)) ^ (2 ^ (4 * R + 3) * h) := by
  have htrial := modeImage_actual_success_count_of_good_event hs hsize hrR
    Q E hr b Success hgoodSuccess
  have hC : 2 ≤ 2 ^ (4 * R + 3) := by
    calc
      2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (4 * R + 3) :=
        Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega)
  apply repeatedSuccessSet_block_amplification
    Success (2 ^ (4 * R + 3)) h hC htrial

end

end CorruptedFieldRecovery
