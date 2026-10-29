import CorruptedFieldRecovery.RawExecutableQuotient

/-! Binary-mask bounds for the raw long-division transition. -/

namespace CorruptedFieldRecovery

/-- If two masks have the same top set bit and no bits above it, their XOR
is strictly below that top power of two. -/
theorem rawXor_lt_two_pow_of_top_bit (a b k : Nat)
    (ha : a.testBit k = true) (hb : b.testBit k = true)
    (habove : ∀ j, k < j → a.testBit j = false)
    (hbabove : ∀ j, k < j → b.testBit j = false) :
    Nat.xor a b < 2 ^ k := by
  apply Nat.lt_of_testBit k
  · simp [Nat.testBit_xor, ha, hb]
  · simp
  · intro j hj
    simp [Nat.testBit_xor, habove j hj, hbabove j hj,
      Nat.testBit_two_pow_of_ne (Ne.symm (ne_of_gt hj))]

/-- The long-division step clears the top bit whenever the current mask and
the shifted modulus have the same leading bit and no higher set bits. -/
theorem rawReduceStep_lt_pow_of_top_bit (modulus degree a : Nat)
    (ha : a.testBit (Nat.log2 a) = true)
    (hshift : (modulus * 2 ^ (Nat.log2 a - degree)).testBit (Nat.log2 a) = true)
    (habove : ∀ j, Nat.log2 a < j → a.testBit j = false)
    (hshiftAbove : ∀ j, Nat.log2 a < j →
      (modulus * 2 ^ (Nat.log2 a - degree)).testBit j = false) :
    rawReduceStep modulus degree a < 2 ^ Nat.log2 a := by
  simpa [rawReduceStep] using
    rawXor_lt_two_pow_of_top_bit a
      (modulus * 2 ^ (Nat.log2 a - degree)) (Nat.log2 a)
      ha hshift habove hshiftAbove

end CorruptedFieldRecovery
