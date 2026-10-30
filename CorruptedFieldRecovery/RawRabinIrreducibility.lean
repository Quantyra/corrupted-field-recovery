import CorruptedFieldRecovery.RawExecutableTraceCertificate

/-! A finite-mask Rabin-style irreducibility route. Polynomial remainder and
Euclidean gcd are computed on Nat masks; Frobenius powers are formed by
repeated quotient squaring. -/

namespace CorruptedFieldRecovery

/-- Nat-mask polynomial remainder by a nonzero mask. The fuel is bounded by
the dividend bit width; the quotient proof is available for every fuel. -/
def rawPolynomialRemainder (dividend divisor : Nat) : Nat :=
  if divisor = 0 then dividend else if divisor = 1 then 0 else
    rawReduceFuel divisor (Nat.log2 divisor) (Nat.log2 dividend + 1) dividend

theorem rawPolynomialRemainder_lt {a b : Nat} (hb : b ≠ 0) :
    rawPolynomialRemainder a b < b := by
  by_cases hb1 : b = 1
  · subst b
    simp [rawPolynomialRemainder]
  have hlow : 2 ^ Nat.log2 b ≤ b := Nat.log2_self_le hb
  have hupp : b < 2 ^ (Nat.log2 b + 1) := Nat.lt_log2_self
  have hs : 0 < Nat.log2 b := by
    by_contra h
    have hz : Nat.log2 b = 0 := by omega
    rw [hz] at hupp
    have hbpos : 0 < b := Nat.pos_of_ne_zero hb
    omega
  have hfuel : Nat.log2 a - Nat.log2 b + 1 ≤ Nat.log2 a + 1 := by omega
  have hrem := rawReduceFuel_lt_of_modulus_band_logFuel
    (s := Nat.log2 b) (modulus := b) (a := a) (fuel := Nat.log2 a + 1)
    hlow hupp hs hfuel
  have hpow := Nat.log2_self_le hb
  unfold rawPolynomialRemainder
  simp only [if_neg hb, if_neg hb1]
  exact lt_of_lt_of_le hrem hpow

/-- Mask remainder preserves the polynomial quotient class modulo the divisor
mask, by the actual bounded Nat reduction. -/
theorem rawPolynomialRemainder_quotient_sound {a b : Nat} (hb : b ≠ 0) :
    AdjoinRoot.mk (rawMaskPolynomial b)
        (rawMaskPolynomial (rawPolynomialRemainder a b)) =
      AdjoinRoot.mk (rawMaskPolynomial b) (rawMaskPolynomial a) := by
  by_cases hb1 : b = 1
  · subst b
    have hpoly : rawMaskPolynomial 1 = (1 : Polynomial (ZMod 2)) := by
      rw [rawMaskPolynomial_step]
      norm_num [rawMaskPolynomial_zero]
    rw [rawPolynomialRemainder, if_neg (by decide : (1 : Nat) ≠ 0), if_pos rfl, hpoly]
    rw [AdjoinRoot.mk_eq_mk]
    refine ⟨-rawMaskPolynomial a, ?_⟩
    rw [rawMaskPolynomial_zero]
    ring
  · unfold rawPolynomialRemainder
    simp only [if_neg hb, if_neg hb1]
    exact rawReduceFuel_quotient_sound b (Nat.log2 b) (Nat.log2 a + 1) a

/-- Euclidean gcd on Nat masks. Each recursive divisor is the canonical
remainder, so the second argument strictly decreases. -/
def rawPolynomialGcd : Nat → Nat → Nat
  | a, 0 => a
  | _, 1 => 1
  | a, b + 2 => rawPolynomialGcd (b + 2) (rawPolynomialRemainder a (b + 2))
termination_by _ b => b
decreasing_by
  exact rawPolynomialRemainder_lt (by omega)

/-- Repeated quotient squaring computes the `d`th Frobenius power of a mask. -/
def rawCandidateFrobeniusAux (modulus : Nat) : Nat → Nat → Nat
  | 0, x => x
  | d + 1, x => rawCandidateFrobeniusAux modulus d
      (rawPolynomialRemainder (rawPolyMul x x) modulus)

def rawCandidateFrobenius {s : Nat} (candidate : RawFieldCandidate s) (d : Nat) : Nat :=
  rawCandidateFrobeniusAux (rawFieldBitsToNat candidate.modulus) d 2

/-- The executable low-degree Frobenius gcd checks: every possible proper
irreducible factor degree is tested against `X^(2^d)-X`. -/
def rawCandidateRabinCheck {s : Nat} (candidate : RawFieldCandidate s) : Bool :=
  (List.range (s / 2)).all fun i => decide
    (rawPolynomialGcd (rawFieldBitsToNat candidate.modulus)
      (Nat.xor (rawCandidateFrobenius candidate (i + 1)) 2) = 1)

/-- Shape gates which are independent of polynomial irreducibility and remain
available before any quotient-field proof is constructed. -/
def rawFieldCandidateShapeCheck {s : Nat} (candidate : RawFieldCandidate s) : Bool :=
  decide (1 ≤ s) && decide (candidate.modulus.size = s + 1) &&
    decide (rawFieldBitsToNat candidate.modulus / 2 ^ s % 2 = 1) &&
    decide (candidate.scalar.size = s) &&
    decide (rawFieldBitsToNat candidate.scalar ≠ 0)

/-- Standalone candidate gate: structural checks plus the bounded Rabin gcd
scan, with no proof or call to the legacy exhaustive factor search. -/
def rawFieldCandidateFastCheck {s : Nat} (candidate : RawFieldCandidate s) : Bool :=
  rawFieldCandidateShapeCheck candidate && rawCandidateRabinCheck candidate

end CorruptedFieldRecovery
