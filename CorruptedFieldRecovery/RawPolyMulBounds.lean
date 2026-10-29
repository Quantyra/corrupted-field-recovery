import CorruptedFieldRecovery.RawReductionLogFuel

/-! Bit-width bounds for carryless multiplication and the resulting reduction
fuel used by the executable finite-field path. -/

namespace CorruptedFieldRecovery

/-- Carryless polynomial multiplication adds the input bit-widths. -/
theorem rawPolyMul_lt_pow (r s a b : Nat)
    (ha : a < 2 ^ r) (hb : b < 2 ^ s) :
    rawPolyMul a b < 2 ^ (r + s) := by
  induction s generalizing r a b with
  | zero =>
      have hb0 : b = 0 := by omega
      simp [rawPolyMul, hb0]
  | succ s ih =>
      by_cases hb0 : b = 0
      · simp [rawPolyMul, hb0]
      · have hhalf : b / 2 < 2 ^ s := by
          apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).2
          simpa [pow_succ, Nat.mul_comm] using hb
        have hproduct := ih r a (b / 2) ha hhalf
        have hshift : 2 * rawPolyMul a (b / 2) < 2 ^ (r + (s + 1)) := by
          calc
            2 * rawPolyMul a (b / 2) < 2 * 2 ^ (r + s) :=
              Nat.mul_lt_mul_of_pos_left hproduct (by decide : 0 < 2)
            _ = 2 ^ (r + s + 1) := by rw [pow_succ]; ring
            _ = 2 ^ (r + (s + 1)) := by congr 1
        have hfirst : (if b % 2 = 1 then a else 0) < 2 ^ (r + (s + 1)) := by
          by_cases hodd : b % 2 = 1
          · simp [hodd]
            exact lt_of_lt_of_le ha (by gcongr <;> omega)
          · simp [hodd]
        rw [rawPolyMul]
        simp only [if_neg hb0]
        apply Nat.bitwise_lt_two_pow
        · exact hfirst
        · exact hshift

/-- Products of two `s`-bit field masks use at most `2s` bits, so the
logarithmic quotient-reduction fuel is bounded by `2s+1`. -/
theorem rawFieldMulFuel_lt_of_accepted_2s {s : Nat}
    (candidate : RawFieldCandidate s)
    (hcheck : rawFieldCandidateCheck candidate = true)
    (a b : Nat) (ha : a < 2 ^ s) (hb : b < 2 ^ s) :
    rawFieldMulFuel candidate (2 * s + 1) a b < 2 ^ s := by
  have hproduct := rawPolyMul_lt_pow s s a b ha hb
  have hvalid := accepted_rawFieldCandidateCheck candidate hcheck
  rcases hvalid with ⟨hs, hmodSize, htop, hscalarSize, hscalar, hirred⟩
  have hlog : Nat.log2 (rawPolyMul a b) < 2 * s := by
    apply rawLog2_lt_of_lt_pow (by omega)
    simpa [two_mul, Nat.add_assoc] using hproduct
  have hmod := accepted_rawCandidateModulusMask_bounds candidate hcheck
  change rawReduceFuel (rawFieldBitsToNat candidate.modulus) s (2 * s + 1)
    (rawPolyMul a b) < 2 ^ s
  exact rawReduceFuel_lt_of_modulus_band_logFuel s
    (rawFieldBitsToNat candidate.modulus) (rawPolyMul a b) (2 * s + 1)
    hmod.1 hmod.2 (by omega) (by omega)

end CorruptedFieldRecovery
