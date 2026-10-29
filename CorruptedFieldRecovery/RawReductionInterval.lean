import CorruptedFieldRecovery.RawReductionBounds

/-! Relate the accepted candidate's numeric mask interval to the raw
long-division step and prove a finite fuel bound. -/

namespace CorruptedFieldRecovery

/-- An accepted raw candidate's modulus mask has exactly its degree `s` as
the highest set-bit position. -/
theorem accepted_rawCandidateModulusMask_bounds {s : Nat}
    (candidate : RawFieldCandidate s)
    (hcheck : rawFieldCandidateCheck candidate = true) :
    2 ^ s ≤ rawFieldBitsToNat candidate.modulus ∧
      rawFieldBitsToNat candidate.modulus < 2 ^ (s + 1) := by
  rcases accepted_rawFieldCandidateCheck candidate hcheck with
    ⟨hs, hsize, htop, hscalarSize, hscalar, hirred⟩
  have hlength : candidate.modulus.toList.length = s + 1 := by
    simpa using hsize
  have hmaskUpper := rawBitsToNat_lt_pow_length candidate.modulus.toList
  have hupper : rawFieldBitsToNat candidate.modulus < 2 ^ (s + 1) := by
    simpa [rawFieldBitsToNat, hlength] using hmaskUpper
  have htop' : rawFieldBitsToNat candidate.modulus / 2 ^ s % 2 = 1 := htop
  have hlower : 2 ^ s ≤ rawFieldBitsToNat candidate.modulus := by
    by_contra h
    have hlt : rawFieldBitsToNat candidate.modulus < 2 ^ s := Nat.lt_of_not_ge h
    rw [Nat.div_eq_of_lt hlt] at htop'
    norm_num at htop'
  exact ⟨hlower, hupper⟩

/-- A natural number in the degree-`k` power-of-two band has its `k`th bit
set. -/
theorem rawTestBit_eq_true_of_power_band {n k : Nat}
    (hlower : 2 ^ k ≤ n) (hupper : n < 2 ^ (k + 1)) :
    n.testBit k = true := by
  have hpow : 0 < 2 ^ k := by positivity
  have hquotLower : 1 ≤ n / 2 ^ k := by
    apply (Nat.le_div_iff_mul_le hpow).2
    simpa [Nat.mul_comm] using hlower
  have hquotUpper : n / 2 ^ k < 2 := by
    apply (Nat.div_lt_iff_lt_mul hpow).2
    simpa [pow_succ, Nat.mul_comm] using hupper
  have hquot : n / 2 ^ k = 1 := by omega
  simp [Nat.testBit, Nat.shiftRight_eq_div_pow, hquot]

/-- A number below `2^(k+1)` has no set bits strictly above position `k`. -/
theorem rawTestBit_eq_false_above_power_band {n k j : Nat}
    (hupper : n < 2 ^ (k + 1)) (hkj : k < j) :
    n.testBit j = false := by
  apply Nat.testBit_eq_false_of_lt
  exact lt_of_lt_of_le hupper (by
    have hexp : k + 1 ≤ j := by omega
    gcongr
    norm_num)

/-- A modulus mask in its degree-`s` band makes every long-division step on a
current mask at least `2^s` strictly decrease the numeric mask. -/
theorem rawReduceStep_lt_of_modulus_band (s modulus a : Nat)
    (hmodLower : 2 ^ s ≤ modulus) (hmodUpper : modulus < 2 ^ (s + 1))
    (hcurrentLower : 2 ^ s ≤ a) :
    rawReduceStep modulus s a < a := by
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
  exact lt_of_lt_of_le hstep hcurrentLower'

/-- `a+1` fuel suffices because every nonterminal reduction strictly
decreases the current mask. This is a finite correctness bound; the efficient
bit-length fuel bound is a separate target. -/
theorem rawReduceFuel_lt_of_modulus_band (s modulus a fuel : Nat)
    (hmodLower : 2 ^ s ≤ modulus) (hmodUpper : modulus < 2 ^ (s + 1))
    (hfuel : a + 1 ≤ fuel) :
    rawReduceFuel modulus s fuel a < 2 ^ s := by
  induction a using Nat.strong_induction_on generalizing fuel with
  | h a ih =>
      by_cases hsmall : a < 2 ^ s
      · cases fuel with
        | zero => omega
        | succ fuel => simp [rawReduceFuel, hsmall]
      · have hcurrentLower : 2 ^ s ≤ a := Nat.le_of_not_gt hsmall
        have hupper := Nat.lt_log2_self (n := a)
        have hdegree : s ≤ Nat.log2 a := by
          have hexp : s < Nat.log2 a + 1 :=
            (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).1
              (lt_of_le_of_lt hcurrentLower hupper)
          omega
        have hstep : rawReduceStep modulus s a < a :=
          rawReduceStep_lt_of_modulus_band s modulus a hmodLower hmodUpper hcurrentLower
        cases fuel with
        | zero => omega
        | succ fuel =>
            have hrecursiveFuel : rawReduceStep modulus s a + 1 ≤ fuel := by omega
            rw [rawReduceFuel, if_neg hsmall]
            exact ih (rawReduceStep modulus s a) hstep fuel hrecursiveFuel

end CorruptedFieldRecovery
