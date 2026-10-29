import CorruptedFieldRecovery.RawPolynomialMaskCompleteness

/-! Ordinary bridge work for the finite raw factor search.  The initial
lemmas pin down the boundedness of its coefficient-mask representation; the
remaining theorem will connect the predicate to `Polynomial.Irreducible`.
No theorem here changes the executable candidate checker.
-/

namespace CorruptedFieldRecovery

open Polynomial

theorem rawMaskPolynomial_step (n : Nat) :
    rawMaskPolynomial n = C (if n.bodd then 1 else 0) +
      X * rawMaskPolynomial n.div2 := by
  cases n with
  | zero => simp [rawMaskPolynomial_zero]
  | succ n =>
      have hn : n + 1 ≠ 0 := by omega
      rw [rawMaskPolynomial_eq_of_ne_zero _ hn]

theorem rawMaskPolynomial_eval_zero (n : Nat) :
    (rawMaskPolynomial n).eval 0 = if n.bodd then 1 else 0 := by
  rw [rawMaskPolynomial_step]
  cases n.bodd <;> simp [eval_add, eval_mul]

theorem rawDivX_X_mul (p : Polynomial (ZMod 2)) :
    Polynomial.divX (X * p) = p := by
  apply Polynomial.ext
  intro i
  simp [Polynomial.coeff_divX]

/-- The mask decoder is injective: its constant coefficient records the low
bit and division by `X` exposes the remaining mask. -/
theorem rawMaskPolynomial_injective {a b : Nat}
    (h : rawMaskPolynomial a = rawMaskPolynomial b) : a = b := by
  suffices hmain : ∀ n a b, a + b = n →
      rawMaskPolynomial a = rawMaskPolynomial b → a = b by
    exact hmain (a + b) a b rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro a b hab heq
      by_cases hn : n = 0
      · subst n
        have ha : a = 0 := by omega
        have hb : b = 0 := by omega
        subst a
        subst b
        rfl
      have hlowEval := congrArg (fun f : Polynomial (ZMod 2) => f.eval 0) heq
      change (rawMaskPolynomial a).eval 0 = (rawMaskPolynomial b).eval 0 at hlowEval
      rw [rawMaskPolynomial_eval_zero, rawMaskPolynomial_eval_zero] at hlowEval
      have hlow : a.bodd = b.bodd := by
        cases ha : a.bodd <;> cases hb : b.bodd <;>
          simp [ha, hb] at hlowEval ⊢
      have hdivPoly : rawMaskPolynomial a.div2 = rawMaskPolynomial b.div2 := by
        have hdiv := congrArg Polynomial.divX heq
        rw [rawMaskPolynomial_step a, rawMaskPolynomial_step b] at hdiv
        cases ha : a.bodd <;> cases hb : b.bodd <;>
          simpa [ha, hb, Nat.div2_val, Polynomial.divX_add, Polynomial.divX_C,
            rawDivX_X_mul] using hdiv
      have hlt : a.div2 + b.div2 < n := by
        rw [Nat.div2_val, Nat.div2_val]
        omega
      have hdiv := ih (a.div2 + b.div2) hlt a.div2 b.div2 rfl hdivPoly
      have hdivQuot : a / 2 = b / 2 := by
        simpa [Nat.div2_val] using hdiv
      have hbits : a % 2 = b % 2 := by
        cases ha : a.bodd <;> cases hb : b.bodd <;>
          simp_all [Nat.mod_two_of_bodd]
      omega

/-- A little-endian list of `n` bits represents a natural below `2^n`.
This is the upper half of the range argument for the finite mask encoding. -/
theorem rawBitsToNat_lt_pow_length (bits : List Bool) :
    rawBitsToNat bits < 2 ^ bits.length := by
  induction bits with
  | nil => simp [rawBitsToNat]
  | cons b bs ih =>
      cases b <;> simp [rawBitsToNat] at * <;> omega

/-- Appending high-end coefficients shifts the suffix mask by the length of
the low-end prefix. -/
theorem rawBitsToNat_append (bits suffix : List Bool) :
    rawBitsToNat (bits ++ suffix) =
      rawBitsToNat bits + 2 ^ bits.length * rawBitsToNat suffix := by
  induction bits with
  | nil => simp [rawBitsToNat]
  | cons b bs ih =>
      simp only [List.cons_append, rawBitsToNat, List.length_cons]
      rw [ih]
      simp only [pow_succ]
      cases b <;> simp <;> ring

theorem rawBitsToNat_append_true (bits : List Bool) :
    rawBitsToNat (bits ++ [true]) = rawBitsToNat bits + 2 ^ bits.length := by
  rw [rawBitsToNat_append]
  simp [rawBitsToNat]

/-- The bounded encoder uses exactly one bit for each coefficient through the
polynomial's leading degree. -/
theorem rawPolynomialBitsFuel_length (fuel : Nat) (p : Polynomial (ZMod 2))
    (hp : p ≠ 0) (hdeg : p.natDegree < fuel) :
    (rawPolynomialBitsFuel fuel p).length = p.natDegree + 1 := by
  induction fuel generalizing p with
  | zero => omega
  | succ fuel ih =>
      by_cases hdiv : p.divX = 0
      · have hdeg0 : p.natDegree = 0 := by
          rw [(divX_eq_zero_iff.mp hdiv)]
          simp
        simp [rawPolynomialBitsFuel, hp, hdiv, rawPolynomialBitsFuel_zero, hdeg0]
      · have hpos : p.natDegree ≠ 0 := by
          intro hzero
          apply hdiv
          rw [eq_C_of_natDegree_eq_zero hzero, divX_C]
        have htail : p.divX.natDegree < fuel := by
          rw [natDegree_divX_eq_natDegree_tsub_one]
          omega
        have hrec := ih p.divX hdiv htail
        have hdegStep : p.divX.natDegree + 1 = p.natDegree := by
          rw [natDegree_divX_eq_natDegree_tsub_one]
          omega
        simp [rawPolynomialBitsFuel, hp, hrec, hdegStep]

theorem rawPolynomialBits_length (p : Polynomial (ZMod 2)) (hp : p ≠ 0) :
    (rawPolynomialBits p).length = p.natDegree + 1 := by
  exact rawPolynomialBitsFuel_length (p.natDegree + 1) p hp (Nat.lt_succ_self _)

def rawBitsEndsTrue (bits : List Bool) : Prop :=
  ∃ preBits, bits = preBits ++ [true]

theorem rawBitsEndsTrue_cons (b : Bool) (bits : List Bool)
    (h : rawBitsEndsTrue bits) : rawBitsEndsTrue (b :: bits) := by
  rcases h with ⟨preBits, rfl⟩
  exact ⟨b :: preBits, by simp [List.cons_append]⟩

theorem monic_divX_of_natDegree_pos {p : Polynomial (ZMod 2)}
    (hp : p.Monic) (hpos : 0 < p.natDegree) : p.divX.Monic := by
  change p.leadingCoeff = 1 at hp
  change p.divX.leadingCoeff = 1
  rw [leadingCoeff, natDegree_divX_eq_natDegree_tsub_one]
  have hidx : p.natDegree - 1 + 1 = p.natDegree := by omega
  calc
    p.divX.coeff (p.natDegree - 1) = p.coeff p.natDegree := by
      rw [coeff_divX, hidx]
    _ = p.leadingCoeff := rfl
    _ = 1 := hp

theorem rawPolynomialBitsFuel_monic_endsTrue (fuel : Nat)
    (p : Polynomial (ZMod 2)) (hp : p.Monic) (hdeg : p.natDegree < fuel) :
    rawBitsEndsTrue (rawPolynomialBitsFuel fuel p) := by
  induction fuel generalizing p with
  | zero => omega
  | succ fuel ih =>
      have hp0 : p ≠ 0 := by
        intro hz
        subst p
        simp at hp
      by_cases hdiv : p.divX = 0
      · have hC : p = C (p.coeff 0) := (divX_eq_zero_iff).mp hdiv
        have hc : p.coeff 0 = 1 := by
          rw [hC] at hp
          simpa [Monic, leadingCoeff] using hp
        simp [rawPolynomialBitsFuel, hp0, hdiv, rawPolynomialBitsFuel_zero,
          rawBitsEndsTrue, hc, rawCoeffBit]
      · have hpos : 0 < p.natDegree := by
          have hn : p.natDegree ≠ 0 := by
            intro hz
            apply hdiv
            rw [eq_C_of_natDegree_eq_zero hz, divX_C]
          omega
        have htailMonic := monic_divX_of_natDegree_pos hp hpos
        have htailDegree : p.divX.natDegree < fuel := by
          rw [natDegree_divX_eq_natDegree_tsub_one]
          omega
        have htail := ih p.divX htailMonic htailDegree
        simp only [rawPolynomialBitsFuel, if_neg hp0]
        exact rawBitsEndsTrue_cons (rawCoeffBit (p.coeff 0)) _ htail

theorem rawPolynomialBits_monic_endsTrue (p : Polynomial (ZMod 2))
    (hp : p.Monic) : rawBitsEndsTrue (rawPolynomialBits p) := by
  exact rawPolynomialBitsFuel_monic_endsTrue (p.natDegree + 1) p hp
    (Nat.lt_succ_self _)

theorem rawPolynomialBits_mask_range (p : Polynomial (ZMod 2))
    (hp : p.Monic) :
    2 ^ p.natDegree ≤ rawBitsToNat (rawPolynomialBits p) ∧
      rawBitsToNat (rawPolynomialBits p) < 2 ^ (p.natDegree + 1) := by
  have hp0 : p ≠ 0 := by
    intro hz
    subst p
    simp at hp
  obtain ⟨preBits, hbits⟩ := rawPolynomialBits_monic_endsTrue p hp
  have hprefix : preBits.length = p.natDegree := by
    have hlen := congrArg List.length hbits
    rw [rawPolynomialBits_length p hp0] at hlen
    simp at hlen
    omega
  have hlower := rawBitsToNat_append_true preBits
  rw [← hbits] at hlower
  constructor
  · rw [hlower, hprefix]
    omega
  · have hup := rawBitsToNat_lt_pow_length (rawPolynomialBits p)
    rw [rawPolynomialBits_length p hp0] at hup
    exact hup

/-- The existing mask decoder agrees with the proof-defined finite
coefficient encoding, so arbitrary polynomial factors can be represented by
finite masks without truncation. -/
theorem rawPolynomialBits_mask_decode (p : Polynomial (ZMod 2)) :
    rawMaskPolynomial (rawBitsToNat (rawPolynomialBits p)) = p := by
  rw [← rawBoolListPolynomial_eq_mask]
  exact rawPolynomialBits_decode p

end CorruptedFieldRecovery
