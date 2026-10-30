import CorruptedFieldRecovery.S010ModeImageFiveCount
import CorruptedFieldRecovery.S010ActualScalarBounds
import CorruptedFieldRecovery.S010BetaArithmetic
import CorruptedFieldRecovery.S010CleanLossBounds
import CorruptedFieldRecovery.S010CountProduct
import Mathlib.Tactic

namespace CorruptedFieldRecovery

open Module

noncomputable section

/-- The accepted actual mode-image five-tape count, combined with the
size-derived beta and the actual scalar-complement count, gives the
cross-multiplied one-trial bound. The coordinate equivalence Q, tensor E,
rank bound, and deterministic basis family remain explicit inputs. -/
theorem modeImage_actual_one_trial_bound
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra BinaryField K] [FiniteDimensional BinaryField K] [Finite K]
    {s R r : Nat} (hs : Module.finrank BinaryField K = s)
    (hsize : 2 * R + 5 ≤ s) (hrR : r ≤ R)
    (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K)
    (E : BinaryTensor (3 * s))
    (hr : Module.finrank BinaryField (modeImageSemanticSupport Q E) = r)
    (b : (Fin 4 → FieldTriple K) → Basis (Fin s) BinaryField K) :
    2 ^ (4 * R + 3) *
        (actualFiveGoodTapeSet K Q (modeImageSemanticCleanFieldSet Q E)
          (modeImageSemanticSupport Q E) b).card ≥
      2 ^ (13 * s) := by
  classical
  let aN : Nat := 2 ^ (3 * s - r)
  let qN : Nat := 2 ^ s
  let T : Nat := ∑ d ∈ properDegrees K, 2 ^ d
  let b₁ : Nat := (nonGenerators K).card * qN ^ 2
  let b₂ : Nat := qN ^ 2
  let b₃ : Nat := qN
  let b₄ : Nat := 1
  let f₁ : Nat := aN - b₁
  let f₂ : Nat := aN - b₂
  let f₃ : Nat := aN - b₃
  let f₄ : Nat := aN - b₄
  let F : Nat := f₁ * (f₂ * (f₃ * f₄))
  let g : Nat := qN - (T + (2 ^ (2 * r) - 1))
  let tapeCount :=
    (actualFiveGoodTapeSet K Q (modeImageSemanticCleanFieldSet Q E)
      (modeImageSemanticSupport Q E) b).card

  have hTau : 4 * (2 ^ R * T) < 2 ^ s := by
    simpa [T] using actual_proper_degree_scaled_bound K s R hs hsize
  have hBeta := @beta_lt_half_from_size s R T hsize (by simpa [T] using hTau)

  let q : ℚ := (qN : ℚ)
  let a : ℚ := (aN : ℚ)
  let p : ℚ := (2 ^ R : ℚ)
  let t : ℚ := (T : ℚ)
  have hq : 0 < q := by dsimp [q, qN]; positivity
  have ha : 0 < a := by dsimp [a, aN]; positivity
  have ht : 0 ≤ t := by positivity
  have hrpow : 2 ^ r ≤ 2 ^ R :=
    Nat.pow_le_pow_right (by decide : 1 ≤ 2) hrR
  have hexp : r + (3 * s - r) = 3 * s := by omega
  have hqcube : (2 ^ s) ^ 3 = 2 ^ (3 * s) := by
    rw [← pow_mul]
    congr 1
    omega
  have hpowfactor : 2 ^ (3 * s) = 2 ^ r * 2 ^ (3 * s - r) := by
    rw [← pow_add, hexp]
  have hgainNat : (2 ^ s) ^ 3 ≤ 2 ^ R * 2 ^ (3 * s - r) := by
    rw [hqcube, hpowfactor]
    exact Nat.mul_le_mul_right _ hrpow
  have hgain : q ^ 3 / a ≤ p := by
    apply (div_le_iff₀ ha).2
    dsimp [q, a, p, qN, aN]
    exact_mod_cast hgainNat

  have hnonGen : (nonGenerators K).card ≤ T := by
    simpa [T] using card_nonGenerators_le_proper_degree_sum K
  have hnonGenQ : ((nonGenerators K).card : ℚ) ≤ t := by
    change ((nonGenerators K).card : ℚ) ≤ (T : ℚ)
    exact_mod_cast hnonGen
  have hbad1 : ((b₁ : Nat) : ℚ) / a ≤ t * q ^ 2 / a := by
    calc
      ((b₁ : Nat) : ℚ) / a =
          ((nonGenerators K).card : ℚ) * q ^ 2 / a := by
        simp [b₁, q, qN]
      _ ≤ t * q ^ 2 / a := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hnonGenQ (sq_nonneg q)) (le_of_lt ha)

  let loss₁ : ℚ := (b₁ : ℚ) / a
  let loss₂ : ℚ := q ^ 2 / a
  let loss₃ : ℚ := q / a
  let loss₄ : ℚ := 1 / a
  have hfourLoss := four_clean_losses_le_beta hq ha ht hgain
  have hloss : loss₁ + loss₂ + loss₃ + loss₄ < 1 / 2 := by
    have hle : loss₁ + loss₂ + loss₃ + loss₄ ≤
        p / q ^ 3 + p / q ^ 2 + p / q + p * t / q := by
      dsimp [loss₁, loss₂, loss₃, loss₄]
      nlinarith [hbad1, hfourLoss]
    have hbeta : p / q ^ 3 + p / q ^ 2 + p / q + p * t / q < 1 / 2 := by
      have hid : p / q ^ 3 + p / q ^ 2 + p / q =
          p * (1 + q + q ^ 2) / q ^ 3 := by
        field_simp [ne_of_gt hq]
      rw [hid]
      simpa [p, q, t, T, qN] using hBeta
    exact lt_of_le_of_lt hle hbeta

  have haNpos : 0 < aN := by dsimp [aN]; positivity
  have hb₁ : b₁ ≤ aN := by
    have hfrac : loss₁ < 1 := by
      have hnonneg₂ : 0 ≤ loss₂ := by positivity
      have hnonneg₃ : 0 ≤ loss₃ := by positivity
      have hnonneg₄ : 0 ≤ loss₄ := by positivity
      linarith
    have hrat : (b₁ : ℚ) ≤ (aN : ℚ) := by
      have hfrac' : (b₁ : ℚ) / (aN : ℚ) < 1 := by
        simpa [loss₁, a] using hfrac
      simpa only [one_mul] using
        (le_of_lt ((div_lt_iff₀ (by positivity)).mp hfrac'))
    exact_mod_cast hrat
  have hb₂ : b₂ ≤ aN := by
    have hfrac : loss₂ < 1 := by
      have hnonneg₁ : 0 ≤ loss₁ := by positivity
      have hnonneg₃ : 0 ≤ loss₃ := by positivity
      have hnonneg₄ : 0 ≤ loss₄ := by positivity
      linarith
    have hrat : (b₂ : ℚ) ≤ (aN : ℚ) := by
      have hfrac' : (b₂ : ℚ) / (aN : ℚ) < 1 := by
        simpa [loss₂, q, a, b₂, qN] using hfrac
      simpa only [one_mul] using
        (le_of_lt ((div_lt_iff₀ (by positivity)).mp hfrac'))
    exact_mod_cast hrat
  have hb₃ : b₃ ≤ aN := by
    have hfrac : loss₃ < 1 := by
      have hnonneg₁ : 0 ≤ loss₁ := by positivity
      have hnonneg₂ : 0 ≤ loss₂ := by positivity
      have hnonneg₄ : 0 ≤ loss₄ := by positivity
      linarith
    have hrat : (b₃ : ℚ) ≤ (aN : ℚ) := by
      have hfrac' : (b₃ : ℚ) / (aN : ℚ) < 1 := by
        simpa [loss₃, q, a, b₃, qN] using hfrac
      simpa only [one_mul] using
        (le_of_lt ((div_lt_iff₀ (by positivity)).mp hfrac'))
    exact_mod_cast hrat
  have hb₄ : b₄ ≤ aN := by
    have hfrac : loss₄ < 1 := by
      have hnonneg₁ : 0 ≤ loss₁ := by positivity
      have hnonneg₂ : 0 ≤ loss₂ := by positivity
      have hnonneg₃ : 0 ≤ loss₃ := by positivity
      linarith
    have hrat : (b₄ : ℚ) ≤ (aN : ℚ) := by
      have hfrac' : (b₄ : ℚ) / (aN : ℚ) < 1 := by
        simpa [loss₄, a, b₄] using hfrac
      simpa only [one_mul] using
        (le_of_lt ((div_lt_iff₀ (by positivity)).mp hfrac'))
    exact_mod_cast hrat

  have hlossSum : (b₁ : ℚ) / aN + (b₂ : ℚ) / aN +
      (b₃ : ℚ) / aN + (b₄ : ℚ) / aN ≤ 1 := by
    have hsum : (b₁ : ℚ) / (aN : ℚ) + (b₂ : ℚ) / (aN : ℚ) +
        (b₃ : ℚ) / (aN : ℚ) + (b₄ : ℚ) / (aN : ℚ) < 1 / 2 := by
      simpa [loss₁, loss₂, loss₃, loss₄, a, q, qN, b₂, b₃, b₄] using hloss
    linarith
  have hnorm := four_nat_sub_factors_normalized_lower haNpos
    hb₁ hb₂ hb₃ hb₄ hlossSum
  have hnormId :
      (((aN - b₁ : Nat) : ℚ) / aN) *
        (((aN - b₂ : Nat) : ℚ) / aN) *
        (((aN - b₃ : Nat) : ℚ) / aN) *
        (((aN - b₄ : Nat) : ℚ) / aN) =
      (F : ℚ) / (aN : ℚ) ^ 4 := by
    rw [Nat.cast_sub hb₁, Nat.cast_sub hb₂, Nat.cast_sub hb₃, Nat.cast_sub hb₄]
    dsimp [F, f₁, f₂, f₃, f₄, a]
    push_cast
    simp only [Nat.cast_sub hb₁, Nat.cast_sub hb₂, Nat.cast_sub hb₃, Nat.cast_sub hb₄]
    field_simp [ne_of_gt ha]
  have hprodHalf : (1 / 2 : ℚ) < (F : ℚ) / (aN : ℚ) ^ 4 := by
    rw [← hnormId]
    have hsum : (b₁ : ℚ) / (aN : ℚ) + (b₂ : ℚ) / (aN : ℚ) +
        (b₃ : ℚ) / (aN : ℚ) + (b₄ : ℚ) / (aN : ℚ) < 1 / 2 := by
      simpa [loss₁, loss₂, loss₃, loss₄, a, q, qN, b₂, b₃, b₄] using hloss
    linarith [hnorm, hsum]
  have hprodRat : (aN : ℚ) ^ 4 ≤ (2 * F : Nat) := by
    have hmul : (1 / 2 : ℚ) * (aN : ℚ) ^ 4 < (F : ℚ) :=
      (lt_div_iff₀ (by positivity : 0 < (aN : ℚ) ^ 4)).mp hprodHalf
    push_cast
    nlinarith [hmul]
  have hprodNat : aN ^ 4 ≤ 2 * F := by
    exact_mod_cast hprodRat

  have hgood := actual_good_scalar_finite_count_lower K s R r hs hrR hsize
  have hbase : aN ^ 4 * qN ≤ 8 * (F * g) := by
    calc
      aN ^ 4 * qN ≤ (2 * F) * (4 * g) := Nat.mul_le_mul hprodNat hgood
      _ = 8 * (F * g) := by ring
  have hcount := modeImage_actualFiveTape_count_lower hs Q E hr b
  have hcountFG : F * g ≤ tapeCount := by
    simpa [F, f₁, f₂, f₃, f₄, g, aN, qN, T, b₁, b₂, b₃, b₄,
      tapeCount] using hcount
  have hscaled : aN ^ 4 * qN ≤ 8 * tapeCount := by
    calc
      aN ^ 4 * qN ≤ 8 * (F * g) := hbase
      _ ≤ 8 * tapeCount := Nat.mul_le_mul_left 8 hcountFG

  have hA4 : aN ^ 4 * qN = 2 ^ (4 * (3 * s - r) + s) := by
    dsimp [aN, qN]
    rw [← pow_mul]
    have hmul : (3 * s - r) * 4 = 4 * (3 * s - r) := by omega
    rw [hmul, ← pow_add]
  have hexp : 13 * s ≤ 4 * R + 4 * (3 * s - r) + s := by omega
  have hpow : 2 ^ (13 * s) ≤ 2 ^ (4 * R + 4 * (3 * s - r) + s) :=
    Nat.pow_le_pow_right (by decide : 1 ≤ 2) hexp
  have hcoef : 2 ^ (4 * R + 3) = 2 ^ (4 * R) * 8 := by
    rw [pow_add]
    norm_num
  calc
    2 ^ (4 * R + 3) * tapeCount =
        2 ^ (4 * R) * (8 * tapeCount) := by rw [hcoef]; ring
    _ ≥ 2 ^ (4 * R) * (aN ^ 4 * qN) := Nat.mul_le_mul_left _ hscaled
    _ = 2 ^ (4 * R + 4 * (3 * s - r) + s) := by rw [hA4]; rw [← pow_add]; ring
    _ ≥ 2 ^ (13 * s) := hpow

end

end CorruptedFieldRecovery
