import CorruptedFieldRecovery.RawFieldTraceAlgebra

/-! Decode the canonical trace representative to the single base-field bit. -/

namespace CorruptedFieldRecovery

open Polynomial AdjoinRoot

/-- A mask below `2^s` decodes to a polynomial of degree below `s`. -/
theorem rawMaskPolynomial_natDegree_lt_pow {s n : Nat} (hs : 0 < s)
    (hn : n < 2 ^ s) :
    (rawMaskPolynomial n).natDegree < s := by
  induction s generalizing n with
  | zero =>
      omega
  | succ s ih =>
      by_cases hs0 : s = 0
      · subst s
        by_cases hn0 : n = 0
        · subst n
          simp [rawMaskPolynomial_zero]
        · have hnlt : n < 2 := by simpa using hn
          have hn1 : n = 1 := by omega
          subst n
          have hone : rawMaskPolynomial 1 = C (1 : ZMod 2) := by
            rw [rawMaskPolynomial_eq_of_ne_zero 1 (by decide)]
            simp [rawMaskPolynomial_zero]
          rw [hone, natDegree_C]
          omega
      · by_cases hn0 : n = 0
        · subst n
          simp [rawMaskPolynomial_zero]
        · rw [rawMaskPolynomial_eq_of_ne_zero n hn0]
          have hdiv : n.div2 < 2 ^ s := by
            rw [Nat.div2]
            apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).2
            rw [pow_succ] at hn
            nlinarith
          have hrec := ih (by omega) hdiv
          have hmul : (Polynomial.X * rawMaskPolynomial n.div2).natDegree < s + 1 := by
            by_cases hp : rawMaskPolynomial n.div2 = 0
            · simp [hp]
            · rw [natDegree_X_mul hp]
              omega
          have hconst : (Polynomial.C (if n.bodd then (1 : ZMod 2) else 0)).natDegree < s + 1 := by
            calc
              _ = 0 := natDegree_C _
              _ < s + 1 := by omega
          exact lt_of_le_of_lt (natDegree_add_le _ _) (max_lt hconst hmul)

/-- The bounded trace mask is exactly the bit representing the base-field
trace, not merely an element with the same quotient class. -/
theorem rawFieldTraceBits_eq_baseBit {s : Nat}
    (candidate : RawFieldCandidate s)
    (hcheck : rawFieldCandidateCheck candidate = true) (x : Nat)
    (hx : x < 2 ^ s) :
    rawFieldTraceBits candidate hcheck x =
      if Algebra.trace (ZMod 2) (AdjoinRoot (rawCandidateModulus candidate))
          (rawCandidateQuotientClass candidate x) = 0 then 0 else 1 := by
  let tr := Algebra.trace (ZMod 2) (AdjoinRoot (rawCandidateModulus candidate))
    (rawCandidateQuotientClass candidate x)
  let bit := if tr = 0 then 0 else 1
  have hs : 0 < s := by
    have hv := accepted_rawFieldCandidateCheck candidate hcheck
    rcases hv with ⟨hs, hmod, htop, hscalarSize, hscalar, hirred⟩
    omega
  have htraceClass := rawFieldTraceBits_quotient_eq_algebraTrace candidate hcheck x
  have htrCases : tr = 0 ∨ tr = 1 := by
    have hval : tr.val < 2 := ZMod.val_lt tr
    have hvalCases : tr.val = 0 ∨ tr.val = 1 := by omega
    rcases hvalCases with hz | ho
    · left
      apply ZMod.val_injective
      rw [ZMod.val_zero]
      exact hz
    · right
      apply ZMod.val_injective
      haveI : Fact (1 < 2) := ⟨by decide⟩
      have hone : (1 : ZMod 2).val = 1 := ZMod.val_one 2
      rw [hone]
      exact ho
  have hconst : rawMaskPolynomial bit = C tr := by
    rcases htrCases with htr | htr
    · simp [bit, tr, htr, rawMaskPolynomial_zero]
    · simp [bit, htr, rawMaskPolynomial]
  have hpoly : rawMaskPolynomial (rawFieldTraceBits candidate hcheck x) = C tr := by
    have hmod := rawFieldCandidateValid_modulus_polynomial candidate
      (accepted_rawFieldCandidateCheck candidate hcheck)
    have hbound := rawFieldTraceBits_lt_pow candidate hcheck x hx
    have hdeg := rawMaskPolynomial_natDegree_lt_pow hs hbound
    have hdegb : (C tr : Polynomial (ZMod 2)).natDegree < s := by
      calc
        _ = 0 := natDegree_C _
        _ < s := hs
    have hmk :
        AdjoinRoot.mk (rawCandidateModulus candidate)
          (rawMaskPolynomial (rawFieldTraceBits candidate hcheck x) - C tr) = 0 := by
      change rawCandidateQuotientClass candidate (rawFieldTraceBits candidate hcheck x) -
        AdjoinRoot.mk (rawCandidateModulus candidate) (C tr) = 0
      rw [htraceClass, AdjoinRoot.mk_C]
      simp [tr]
    by_contra hneq
    have hdiff :
        rawMaskPolynomial (rawFieldTraceBits candidate hcheck x) - C tr ≠ 0 :=
      sub_ne_zero.mpr hneq
    have hdegdiff :
        (rawMaskPolynomial (rawFieldTraceBits candidate hcheck x) - C tr).natDegree < s := by
      exact lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt hdeg hdegb)
    have hmodDegree : (rawCandidateModulus candidate).natDegree = s := by
      simpa [rawCandidateModulus] using hmod.2
    have hdegdiff' :
        (rawMaskPolynomial (rawFieldTraceBits candidate hcheck x) - C tr).natDegree <
          (rawCandidateModulus candidate).natDegree := by
      rw [hmodDegree]
      exact hdegdiff
    exact (AdjoinRoot.mk_ne_zero_of_natDegree_lt hmod.1 hdiff hdegdiff') hmk
  have hmask := rawMaskPolynomial_injective (hpoly.trans hconst.symm)
  simpa [tr, bit] using hmask

end CorruptedFieldRecovery
