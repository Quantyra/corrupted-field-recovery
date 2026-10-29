import CorruptedFieldRecovery.RawFieldArrayPolynomial
import Mathlib.Algebra.Polynomial.Inductions

/-! Completeness of the finite coefficient-bit encoding for binary
polynomials. This is the first bridge from arbitrary polynomial factors to
the raw masks searched by the executable divisor gate.
-/

namespace CorruptedFieldRecovery

open Polynomial

def rawCoeffBit (c : ZMod 2) : Bool := decide (c = 1)

theorem zmodTwo_eq_zero_or_one (c : ZMod 2) : c = 0 ∨ c = 1 := by
  have hv := c.val_lt
  have hvCases : c.val = 0 ∨ c.val = 1 := by omega
  rcases hvCases with h0 | h1
  · left
    apply (ZMod.val_injective 2)
    simp [h0]
  · right
    apply (ZMod.val_injective 2)
    simp [h1, ZMod.val_one]

theorem rawCoeffBit_sound (c : ZMod 2) :
    (if rawCoeffBit c then (1 : ZMod 2) else 0) = c := by
  rcases zmodTwo_eq_zero_or_one c with h0 | h1
  · simp [rawCoeffBit, h0]
  · simp [rawCoeffBit, h1]

/-- Finite-fuel low-endian coefficient list. Fuel `natDegree p + 1` suffices. -/
noncomputable def rawPolynomialBitsFuel : Nat → Polynomial (ZMod 2) → List Bool
  | 0, _ => []
  | fuel + 1, p =>
      if p = 0 then [] else rawCoeffBit (p.coeff 0) :: rawPolynomialBitsFuel fuel p.divX

theorem rawPolynomialBitsFuel_zero (fuel : Nat) :
    rawPolynomialBitsFuel fuel (0 : Polynomial (ZMod 2)) = [] := by
  cases fuel <;> simp [rawPolynomialBitsFuel]

theorem rawPolynomialBitsFuel_decode (fuel : Nat) (p : Polynomial (ZMod 2))
    (hdeg : p.natDegree < fuel) :
    rawBoolListPolynomial (rawPolynomialBitsFuel fuel p) = p := by
  induction fuel generalizing p with
  | zero => omega
  | succ fuel ih =>
    by_cases hp : p = 0
    · simp [rawPolynomialBitsFuel, hp, rawBoolListPolynomial]
    · by_cases hdiv : p.divX = 0
      · have hpC : p = C (p.coeff 0) := (divX_eq_zero_iff).mp hdiv
        have hbits : rawPolynomialBitsFuel (fuel + 1) p = [rawCoeffBit (p.coeff 0)] := by
          simp [rawPolynomialBitsFuel, hp, hdiv, rawPolynomialBitsFuel_zero]
        rw [hbits]
        simp only [rawBoolListPolynomial]
        have hcoeff := rawCoeffBit_sound (p.coeff 0)
        rw [show C (if rawCoeffBit (p.coeff 0) then (1 : ZMod 2) else 0) = C (p.coeff 0)
          from congrArg C hcoeff]
        simpa using hpC.symm
      · have hdegPos : p.natDegree ≠ 0 := by
          intro h0
          have hpC := eq_C_of_natDegree_eq_zero h0
          apply hdiv
          rw [hpC, divX_C]
        have htail : p.divX.natDegree < fuel := by
          rw [natDegree_divX_eq_natDegree_tsub_one]
          omega
        have hdecodeTail := ih p.divX htail
        have hbits : rawPolynomialBitsFuel (fuel + 1) p =
            rawCoeffBit (p.coeff 0) :: rawPolynomialBitsFuel fuel p.divX := by
          simp [rawPolynomialBitsFuel, hp]
        rw [hbits, rawBoolListPolynomial, hdecodeTail]
        have hcoeff := rawCoeffBit_sound (p.coeff 0)
        rw [show C (if rawCoeffBit (p.coeff 0) then (1 : ZMod 2) else 0) = C (p.coeff 0)
          from congrArg C hcoeff]
        exact (add_comm _ _).trans (X_mul_divX_add p)

noncomputable def rawPolynomialBits (p : Polynomial (ZMod 2)) : List Bool :=
  rawPolynomialBitsFuel (p.natDegree + 1) p

theorem rawPolynomialBits_decode (p : Polynomial (ZMod 2)) :
    rawBoolListPolynomial (rawPolynomialBits p) = p := by
  apply rawPolynomialBitsFuel_decode
  exact Nat.lt_succ_self _

end CorruptedFieldRecovery
