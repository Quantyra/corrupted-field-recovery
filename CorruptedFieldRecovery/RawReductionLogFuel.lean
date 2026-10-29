import CorruptedFieldRecovery.RawReductionInterval

/-! Logarithmic-fuel correctness for the executable quotient reduction. -/

namespace CorruptedFieldRecovery

/-- A positive power-band exponent and an upper bound imply a strict log2
bound. -/
theorem rawLog2_lt_of_lt_pow {n L : Nat} (hL : 0 < L)
    (hn : n < 2 ^ L) : Nat.log2 n < L := by
  by_contra hnot
  have hge : L ≤ Nat.log2 n := Nat.le_of_not_gt hnot
  by_cases hn0 : n = 0
  · have hLzero : L = 0 := by simpa [hn0] using hge
    omega
  · have hpow : 2 ^ L ≤ n := (Nat.le_log2 hn0).mp hge
    omega

/-- In a modulus band, each nonterminal step falls below the current leading
power of two, not just below the current mask. -/
theorem rawReduceStep_lt_pow_of_modulus_band (s modulus a : Nat)
    (hmodLower : 2 ^ s ≤ modulus) (hmodUpper : modulus < 2 ^ (s + 1))
    (hcurrentLower : 2 ^ s ≤ a) :
    rawReduceStep modulus s a < 2 ^ Nat.log2 a := by
  let L := Nat.log2 a
  have hdegree : s ≤ L := by
    have hupper := Nat.lt_log2_self (n := a)
    have hexp : s < L + 1 :=
      (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).1
        (lt_of_le_of_lt hcurrentLower hupper)
    omega
  have hcurrentLower' : 2 ^ L ≤ a := Nat.log2_self_le (by omega)
  have hcurrentUpper : a < 2 ^ (L + 1) := Nat.lt_log2_self
  let shift := L - s
  have hshiftLower : 2 ^ L ≤ modulus * 2 ^ shift := by
    have hexp : s + shift = L := Nat.add_sub_of_le hdegree
    calc
      2 ^ L = 2 ^ s * 2 ^ shift := by rw [← pow_add, hexp]
      _ ≤ modulus * 2 ^ shift := Nat.mul_le_mul_right (2 ^ shift) hmodLower
  have hshiftUpper : modulus * 2 ^ shift < 2 ^ (L + 1) := by
    have hmul := Nat.mul_lt_mul_of_pos_right hmodUpper (by positivity : 0 < 2 ^ shift)
    have hexp : (s + 1) + shift = L + 1 := by dsimp [shift]; omega
    calc
      modulus * 2 ^ shift < 2 ^ (s + 1) * 2 ^ shift := hmul
      _ = 2 ^ (L + 1) := by rw [← pow_add, hexp]
  have hcurrentBit := rawTestBit_eq_true_of_power_band hcurrentLower' hcurrentUpper
  have hshiftBit := rawTestBit_eq_true_of_power_band hshiftLower hshiftUpper
  have hcurrentAbove : ∀ j, L < j → a.testBit j = false :=
    fun j hj => rawTestBit_eq_false_above_power_band hcurrentUpper hj
  have hshiftAbove : ∀ j, L < j → (modulus * 2 ^ shift).testBit j = false :=
    fun j hj => rawTestBit_eq_false_above_power_band hshiftUpper hj
  have hstep := rawReduceStep_lt_pow_of_top_bit modulus s a
    (by simpa [L] using hcurrentBit) (by simpa [L, shift] using hshiftBit)
    (by simpa [L] using hcurrentAbove) (by simpa [L, shift] using hshiftAbove)
  simpa [L] using hstep

/-- Any fuel at least `log2(a)-s+1` reaches a reduced representative of degree
less than `s`. Each active step lowers the log2 measure by at least one. -/
theorem rawReduceFuel_lt_of_modulus_band_logFuel (s modulus a fuel : Nat)
    (hmodLower : 2 ^ s ≤ modulus) (hmodUpper : modulus < 2 ^ (s + 1))
    (hs : 0 < s)
    (hfuel : Nat.log2 a - s + 1 ≤ fuel) :
    rawReduceFuel modulus s fuel a < 2 ^ s := by
  have haux : ∀ L a fuel, Nat.log2 a = L → L - s + 1 ≤ fuel →
      rawReduceFuel modulus s fuel a < 2 ^ s := by
    intro L
    induction L using Nat.strong_induction_on with
    | h L ih =>
        intro a fuel hlog hfuel
        by_cases hsmall : a < 2 ^ s
        · cases fuel <;> simp [rawReduceFuel, hsmall]
        · have hcurrentLower : 2 ^ s ≤ a := Nat.le_of_not_gt hsmall
          have hdegree : s ≤ L := by
            have hupper : a < 2 ^ (L + 1) := by
              simpa [hlog] using (Nat.lt_log2_self (n := a))
            have hexp : s < L + 1 :=
              (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).1
                (lt_of_le_of_lt hcurrentLower hupper)
            omega
          cases fuel with
          | zero => omega
          | succ fuel =>
              rw [rawReduceFuel, if_neg hsmall]
              have hstepBound := rawReduceStep_lt_pow_of_modulus_band
                s modulus a hmodLower hmodUpper hcurrentLower
              have hstepLog : Nat.log2 (rawReduceStep modulus s a) < L := by
                apply rawLog2_lt_of_lt_pow (by omega)
                simpa [hlog] using hstepBound
              by_cases hstepSmall : rawReduceStep modulus s a < 2 ^ s
              · cases fuel <;> simp [rawReduceFuel, hstepSmall]
              · have hstepLower : 2 ^ s ≤ rawReduceStep modulus s a :=
                  Nat.le_of_not_gt hstepSmall
                have hstepDegree : s ≤ Nat.log2 (rawReduceStep modulus s a) := by
                  have hstepUpper := Nat.lt_log2_self
                    (n := rawReduceStep modulus s a)
                  have hexp : s < Nat.log2 (rawReduceStep modulus s a) + 1 :=
                    (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).1
                      (lt_of_le_of_lt hstepLower hstepUpper)
                  omega
                have hrecursiveFuel :
                    Nat.log2 (rawReduceStep modulus s a) - s + 1 ≤ fuel := by
                  omega
                exact ih _ hstepLog _ _ rfl hrecursiveFuel
  exact haux (Nat.log2 a) a fuel rfl hfuel

/-- The executable raw field multiplication uses the accepted modulus mask
and requires only log2-linear reduction fuel in its Nat product operand. -/
theorem rawFieldMulFuel_lt_of_accepted {s : Nat}
    (candidate : RawFieldCandidate s)
    (hcheck : rawFieldCandidateCheck candidate = true)
    (a b : Nat) :
    rawFieldMulFuel candidate
        (Nat.log2 (rawPolyMul a b) - s + 1) a b < 2 ^ s := by
  have hmod := accepted_rawCandidateModulusMask_bounds candidate hcheck
  have hvalid := accepted_rawFieldCandidateCheck candidate hcheck
  rcases hvalid with ⟨hsNat, hmodSize, htop, hscalarSize, hscalar, hirred⟩
  change rawReduceFuel (rawFieldBitsToNat candidate.modulus) s
    (Nat.log2 (rawPolyMul a b) - s + 1) (rawPolyMul a b) < 2 ^ s
  exact rawReduceFuel_lt_of_modulus_band_logFuel (s := s)
    (rawFieldBitsToNat candidate.modulus) (rawPolyMul a b)
    (Nat.log2 (rawPolyMul a b) - s + 1) hmod.1 hmod.2
    (by omega) (by rfl)

end CorruptedFieldRecovery
