import CorruptedFieldRecovery.RawFieldCandidate
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Field.ZMod

/-! Semantic bridge from raw natural-number bit masks to binary polynomials.

The decoder is proof-only. It interprets bit `i` as the coefficient of `X^i`.
The raw candidate checker itself remains finite Boolean/Nat computation.
-/

namespace CorruptedFieldRecovery

open Polynomial

noncomputable def rawMaskPolynomial (n : Nat) : Polynomial (ZMod 2) :=
  if n = 0 then 0 else
    C (if n.bodd then 1 else 0) + X * rawMaskPolynomial n.div2
termination_by n
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero (by assumption)) (by decide)

theorem rawMaskPolynomial_zero : rawMaskPolynomial 0 = 0 := by
  simp [rawMaskPolynomial]

theorem rawMaskPolynomial_eq_of_ne_zero (n : Nat) (hn : n ≠ 0) :
    rawMaskPolynomial n = C (if n.bodd then 1 else 0) + X * rawMaskPolynomial n.div2 := by
  rw [rawMaskPolynomial, if_neg hn]

theorem rawMaskPolynomial_bit (b : Bool) (n : Nat) :
    rawMaskPolynomial (Nat.bit b n) = C (if b then 1 else 0) + X * rawMaskPolynomial n := by
  cases b
  · by_cases hn : n = 0
    · subst n
      change rawMaskPolynomial 0 = C (0 : ZMod 2) + X * rawMaskPolynomial 0
      rw [rawMaskPolynomial_zero]
      simp
    · have hbit : Nat.bit false n ≠ 0 := Nat.bit_ne_zero false hn
      rw [rawMaskPolynomial_eq_of_ne_zero _ hbit]
      simp
  · have hbit : Nat.bit true n ≠ 0 := by
      cases n with
      | zero => simp [Nat.bit]
      | succ n => exact Nat.bit_ne_zero true (by omega)
    rw [rawMaskPolynomial_eq_of_ne_zero _ hbit]
    simp

theorem rawMaskPolynomial_shift (n : Nat) :
    rawMaskPolynomial (2 * n) = X * rawMaskPolynomial n := by
  have hbit : Nat.bit false n = 2 * n := by simp [Nat.bit]
  rw [← hbit, rawMaskPolynomial_bit]
  simp

theorem rawMaskPolynomial_xor (a b : Nat) :
    rawMaskPolynomial (Nat.xor a b) = rawMaskPolynomial a + rawMaskPolynomial b := by
  suffices hmain : ∀ n a b, a + b = n →
      rawMaskPolynomial (Nat.xor a b) = rawMaskPolynomial a + rawMaskPolynomial b by
    exact hmain (a + b) a b rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a b hab
    change rawMaskPolynomial (Nat.bitwise bne a b) = _
    by_cases ha : a = 0
    · subst a
      rw [Nat.bitwise_zero_left, rawMaskPolynomial_zero]
      simp
    by_cases hb : b = 0
    · subst b
      rw [Nat.bitwise_zero_right, rawMaskPolynomial_zero]
      simp
    rw [Nat.bitwise_of_ne_zero ha hb, rawMaskPolynomial_bit]
    have hlt : a / 2 + b / 2 < n := by omega
    have hrec := ih (a / 2 + b / 2) hlt (a / 2) (b / 2) rfl
    have hrec' : rawMaskPolynomial (Nat.bitwise bne (a / 2) (b / 2)) =
        rawMaskPolynomial (a / 2) + rawMaskPolynomial (b / 2) := by
      change rawMaskPolynomial (Nat.xor (a / 2) (b / 2)) = _
      exact hrec
    rw [hrec', rawMaskPolynomial_eq_of_ne_zero a ha,
      rawMaskPolynomial_eq_of_ne_zero b hb]
    have hbitCoeff :
        (if Nat.bodd a != Nat.bodd b then (1 : ZMod 2) else 0) =
          (if Nat.bodd a then 1 else 0) + (if Nat.bodd b then 1 else 0) := by
      have htwo : (1 : ZMod 2) + 1 = 0 := ZModModule.add_self 1
      cases Nat.bodd a <;> cases Nat.bodd b <;> simp [htwo]
    have hbit : C (if Nat.bodd a != Nat.bodd b then (1 : ZMod 2) else 0) =
        C (if Nat.bodd a then 1 else 0) + C (if Nat.bodd b then 1 else 0) := by
      rw [← C_add]
      exact congrArg C hbitCoeff
    rw [hbit]
    simp only [Nat.div2_val]
    ring

theorem rawPolyMul_polynomial (a b : Nat) :
    rawMaskPolynomial (rawPolyMul a b) = rawMaskPolynomial a * rawMaskPolynomial b := by
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
    by_cases hb : b = 0
    · subst b
      simp [rawPolyMul, rawMaskPolynomial_zero]
    rw [rawPolyMul]
    simp only [if_neg hb]
    rw [rawMaskPolynomial_xor, rawMaskPolynomial_shift]
    have ih' := ih (b / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero hb) (by decide)) a
    rw [ih']
    have hbit : rawMaskPolynomial (if b % 2 = 1 then a else 0) =
        (if b % 2 = 1 then rawMaskPolynomial a else 0) := by
      by_cases hodd : b % 2 = 1 <;> simp [hodd, rawMaskPolynomial_zero]
    rw [hbit]
    rw [rawMaskPolynomial_eq_of_ne_zero b hb]
    have hbodd : b.bodd = decide (b % 2 = 1) := by
      cases h : b.bodd <;> simp [Nat.mod_two_of_bodd, h]
    by_cases hodd : b % 2 = 1 <;> simp [hbodd, hodd, Nat.div2_val] <;> ring

end CorruptedFieldRecovery
