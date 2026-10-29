import CorruptedFieldRecovery.RawFieldPolynomialBridge

/-! Bridge from the serialized little-endian Bool arrays to the proof-only
Nat-mask polynomial decoder. -/

namespace CorruptedFieldRecovery

open Polynomial

noncomputable def rawBoolListPolynomial : List Bool → Polynomial (ZMod 2)
  | [] => 0
  | b :: bs => C (if b then 1 else 0) + X * rawBoolListPolynomial bs

theorem rawBitsToNat_cons (b : Bool) (bs : List Bool) :
    rawBitsToNat (b :: bs) = Nat.bit b (rawBitsToNat bs) := by
  cases b
  · simp [rawBitsToNat, Nat.bit]
  · simp [rawBitsToNat, Nat.bit]
    omega

theorem rawBoolListPolynomial_eq_mask (bits : List Bool) :
    rawBoolListPolynomial bits = rawMaskPolynomial (rawBitsToNat bits) := by
  induction bits with
  | nil => simp [rawBoolListPolynomial, rawBitsToNat, rawMaskPolynomial_zero]
  | cons b bs ih =>
    change C (if b then 1 else 0) + X * rawBoolListPolynomial bs = _
    rw [rawBitsToNat_cons, rawMaskPolynomial_bit, ih]

noncomputable def rawFieldArrayPolynomial (bits : RawFieldBits) : Polynomial (ZMod 2) :=
  rawBoolListPolynomial bits.toList

theorem rawFieldArrayPolynomial_eq_mask (bits : RawFieldBits) :
    rawFieldArrayPolynomial bits = rawMaskPolynomial (rawFieldBitsToNat bits) := by
  simpa [rawFieldArrayPolynomial, rawFieldBitsToNat] using
    rawBoolListPolynomial_eq_mask bits.toList

end CorruptedFieldRecovery
