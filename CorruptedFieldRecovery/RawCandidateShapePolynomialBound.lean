import CorruptedFieldRecovery.RawCandidateShapeCostBounds

/-! Polynomial envelope for the explicit short-circuit shape-check charge,
parameterized by candidate degree and the two raw input lengths. -/

namespace CorruptedFieldRecovery

private theorem rawNatBitWidth_le_add_one (n : Nat) :
    rawNatBitWidth n ≤ n + 1 := by
  unfold rawNatBitWidth
  have h := Nat.log2_le_self n
  omega

private theorem rawNatBitWidth_le_of_lt_pow_public {n k : Nat}
    (hn : n < 2 ^ k) : rawNatBitWidth n ≤ k + 1 := by
  by_cases hzero : n = 0
  · simp [rawNatBitWidth, hzero]
  · have hk : 0 < k := by
      cases k with
      | zero => simp at hn; omega
      | succ k => omega
    have hlog := rawLog2_lt_of_lt_pow hk hn
    unfold rawNatBitWidth
    omega

set_option maxHeartbeats 2000000 in
/-- For either success or early failure, the shape gate's executed declared
charge is quadratic in total input width. The envelope assumes only the
provided degree and array lengths; it does not assume a well-shaped input. -/
theorem rawFieldCandidateShapeCheckBitCosted_polynomial_bound {s : Nat}
    (candidate : RawFieldCandidate s) :
    (rawFieldCandidateShapeCheckBitCosted candidate).2 ≤
      100 * (s + candidate.modulus.size + candidate.scalar.size + 4) ^ 2 := by
  let m := candidate.modulus.size
  let n := candidate.scalar.size
  let b := s + m + n + 4
  have hb : 4 ≤ b := by dsimp [b, m, n]; omega
  have hm : m ≤ b := by dsimp [b, m, n]; omega
  have hn : n ≤ b := by dsimp [b, m, n]; omega
  have hs : s ≤ b := by dsimp [b, m, n]; omega
  have hmp3 : m + 3 ≤ b := by dsimp [b, m, n]; omega
  have hnp3 : n + 3 ≤ b := by dsimp [b, m, n]; omega
  have hwidthS : rawNatBitWidth s ≤ b := by
    exact le_trans (rawNatBitWidth_le_add_one s) (by dsimp [b, m, n]; omega)
  have hwidthM : rawNatBitWidth m ≤ b := by
    exact le_trans (rawNatBitWidth_le_add_one m) (by dsimp [b, m, n]; omega)
  have hwidthN : rawNatBitWidth n ≤ b := by
    exact le_trans (rawNatBitWidth_le_add_one n) (by dsimp [b, m, n]; omega)
  have hmodLt : rawFieldBitsToNat candidate.modulus < 2 ^ m := by
    have h := rawBitsToNat_lt_pow_length candidate.modulus.toList
    simpa [rawFieldBitsToNat, m] using h
  have hscalarLt : rawFieldBitsToNat candidate.scalar < 2 ^ n := by
    have h := rawBitsToNat_lt_pow_length candidate.scalar.toList
    simpa [rawFieldBitsToNat, n] using h
  have hmodWidth : rawNatBitWidth (rawFieldBitsToNat candidate.modulus) ≤ b := by
    exact le_trans (rawNatBitWidth_le_of_lt_pow_public hmodLt)
      (by dsimp [b, m, n]; omega)
  have hscalarWidth : rawNatBitWidth (rawFieldBitsToNat candidate.scalar) ≤ b := by
    exact le_trans (rawNatBitWidth_le_of_lt_pow_public hscalarLt)
      (by dsimp [b, m, n]; omega)
  have hpowPos : 0 < 2 ^ s := Nat.pow_pos (by decide)
  have hpowLt : 2 ^ s < 2 ^ (s + 1) := by
    rw [pow_succ]
    nlinarith
  have hpowWidth : rawNatBitWidth (2 ^ s) ≤ b := by
    exact le_trans (rawNatBitWidth_le_of_lt_pow_public hpowLt)
      (by dsimp [b, m, n]; omega)
  have hquotLe : rawFieldBitsToNat candidate.modulus / 2 ^ s ≤
      rawFieldBitsToNat candidate.modulus := Nat.div_le_self _ _
  have hquotLt : rawFieldBitsToNat candidate.modulus / 2 ^ s < 2 ^ m :=
    lt_of_le_of_lt hquotLe hmodLt
  have hquotWidth : rawNatBitWidth
      (rawFieldBitsToNat candidate.modulus / 2 ^ s) ≤ b := by
    exact le_trans (rawNatBitWidth_le_of_lt_pow_public hquotLt)
      (by dsimp [b, m, n]; omega)
  have hresidueLt : rawFieldBitsToNat candidate.modulus / 2 ^ s % 2 < 2 :=
    Nat.mod_lt _ (by decide)
  have hresidueWidth : rawNatBitWidth
      (rawFieldBitsToNat candidate.modulus / 2 ^ s % 2) ≤ b := by
    exact le_trans (rawNatBitWidth_le_of_lt_pow_public (k := 1) hresidueLt)
      (by dsimp [b, m, n]; omega)
  have hmodCost := rawFieldBitsToNatBitCosted_cost_le candidate.modulus
  have hmodProduct : m * (m + 3) ≤ b * b := Nat.mul_le_mul hm hmp3
  have hscalarCost := rawFieldBitsToNatBitCosted_cost_le candidate.scalar
  have hscalarProduct : n * (n + 3) ≤ b * b := Nat.mul_le_mul hn hnp3
  have hdivMod : rawShapeDivisionCharge
      (rawFieldBitsToNat candidate.modulus) (2 ^ s) ≤ 32 * b ^ 2 := by
    unfold rawShapeDivisionCharge
    have hsum : rawNatBitWidth (rawFieldBitsToNat candidate.modulus) +
        rawNatBitWidth (2 ^ s) + 1 ≤ 4 * b := by omega
    have hsq := Nat.pow_le_pow_left hsum
    nlinarith [hsq]
  have hdivQuot : rawShapeDivisionCharge
      (rawFieldBitsToNat candidate.modulus / 2 ^ s) 2 ≤ 32 * b ^ 2 := by
    unfold rawShapeDivisionCharge
    have hsum : rawNatBitWidth
        (rawFieldBitsToNat candidate.modulus / 2 ^ s) +
        rawNatBitWidth 2 + 1 ≤ 4 * b := by
      have htwo : rawNatBitWidth 2 ≤ b := by
        exact le_trans (rawNatBitWidth_le_of_lt_pow_public (by decide : 2 < 2 ^ 2))
          (by dsimp [b, m, n]; omega)
      omega
    have hsq := Nat.pow_le_pow_left hsum
    nlinarith [hsq]
  have hlinear :
      rawShapeCompareCharge 1 s + rawShapeCompareCharge m (s + 1) + s +
        rawShapeCompareCharge
          (rawFieldBitsToNat candidate.modulus / 2 ^ s % 2) 1 +
        rawShapeCompareCharge n s +
        rawNatBitWidth (rawFieldBitsToNat candidate.scalar) ≤ 10 * b := by
    unfold rawShapeCompareCharge
    have hwidthSsucc : rawNatBitWidth (s + 1) ≤ b := by
      exact le_trans (rawNatBitWidth_le_add_one (s + 1))
        (by dsimp [b, m, n]; omega)
    have hone : rawNatBitWidth 1 ≤ b := by
      exact le_trans (rawNatBitWidth_le_add_one 1) (by dsimp [b, m, n]; omega)
    omega
  change (rawFieldCandidateShapeCheckBitCosted candidate).2 ≤ 100 * b ^ 2
  calc
    (rawFieldCandidateShapeCheckBitCosted candidate).2 ≤
        rawFieldCandidateShapeWorstCaseCharge candidate :=
          rawFieldCandidateShapeCheckBitCosted_cost_le_worst candidate
    _ ≤ 10 * b + b ^ 2 + b ^ 2 + 32 * b ^ 2 + 32 * b ^ 2 := by
      unfold rawFieldCandidateShapeWorstCaseCharge
      nlinarith [hmodCost, hmodProduct, hscalarCost, hscalarProduct,
        hdivMod, hdivQuot, hlinear]
    _ ≤ 100 * b ^ 2 := by nlinarith [hb]

end CorruptedFieldRecovery
