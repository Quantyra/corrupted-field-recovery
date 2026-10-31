import CorruptedFieldRecovery.RawArithmeticFrobeniusNestedStackTrace

/-! Charge and explicit live-bit bounds for the composed repeated-square
Frobenius snapshots. The recurrence charges the actual multiplier path and
the reducer fuel bound at each iteration. It is a declared abstract trace
model, not Lean evaluator time, stack, or heap usage. -/

namespace CorruptedFieldRecovery

/-- The number of frames charged for the nested Frobenius trace. One parent
frame is charged per iteration, together with the multiplier's declared
charge, the reducer's fuel-plus-terminal-frame allowance, and the child. -/
def rawCandidateFrobeniusNestedCharge (modulus : Nat) : Nat → Nat → Nat
  | 0, _ => 1
  | d + 1, x =>
      let square := rawPolyMulBitCosted x x
      let rem := rawPolynomialRemainderBitCosted square.1 modulus
      1 + (rawPolyMulBitCosted x x).2 +
        (Nat.log2 square.1 + 2) +
        rawCandidateFrobeniusNestedCharge modulus d rem.1
termination_by d _ => d
decreasing_by omega

private theorem rawArithmeticPrefixStackTrace_length_le_frob
    (frames : RawArithmeticStack) :
    ∀ stack ∈ rawArithmeticPrefixStackTrace frames,
      stack.length ≤ frames.length := by
  induction frames with
  | nil => simp [rawArithmeticPrefixStackTrace]
  | cons frame tail ih =>
      intro stack hstack
      simp only [rawArithmeticPrefixStackTrace, List.mem_append,
        List.mem_singleton, List.mem_map] at hstack
      rcases hstack with hhead | ⟨tailStack, htail, rfl⟩
      · subst stack
        simp
      · have h := ih tailStack htail
        simp only [List.length_cons]
        omega

/-- Every composed stack snapshot is bounded by the recurrence charging its
parent, actual multiplication trace, reducer fuel, and recursive child. -/
theorem rawCandidateFrobeniusNestedStackTrace_length_le_charge
    (modulus d x : Nat) :
    ∀ stack ∈ rawCandidateFrobeniusNestedStackTrace modulus d x,
      stack.length ≤ rawCandidateFrobeniusNestedCharge modulus d x := by
  induction d generalizing x with
  | zero =>
      intro stack hstack
      simp only [rawCandidateFrobeniusNestedStackTrace,
        List.mem_singleton] at hstack
      subst stack
      simp [rawCandidateFrobeniusNestedCharge]
  | succ d ih =>
      let square := rawPolyMulBitCosted x x
      let rem := rawPolynomialRemainderBitCosted square.1 modulus
      let reduceTrace := rawReduceFuelActivationTrace modulus
        (Nat.log2 modulus) (Nat.log2 square.1 + 1) square.1
      have hcharge : rawCandidateFrobeniusNestedCharge modulus (d + 1) x =
          1 + (rawPolyMulBitCosted x x).2 +
            (Nat.log2 (rawPolyMulBitCosted x x).1 + 2) +
            rawCandidateFrobeniusNestedCharge modulus d
              (rawPolynomialRemainderBitCosted
                (rawPolyMulBitCosted x x).1 modulus).1 := by
        simp only [rawCandidateFrobeniusNestedCharge]
      have hreduce := rawReduceFuelActivationTrace_length_le modulus
        (Nat.log2 modulus) (Nat.log2 square.1 + 1) square.1
      dsimp [square, rem] at hreduce
      intro stack hstack
      simp only [rawCandidateFrobeniusNestedStackTrace] at hstack
      rw [List.mem_append] at hstack
      rw [hcharge]
      rcases hstack with hleft | hchildStack
      · rw [List.mem_append] at hleft
        rcases hleft with hleft | hreduceStack
        · rw [List.mem_append] at hleft
          rcases hleft with hroot | hmulStack
          · simp only [List.mem_singleton] at hroot
            subst stack
            simp only [List.length_singleton]
            omega
          · simp only [List.mem_map] at hmulStack
            rcases hmulStack with ⟨mstack, hmstack, rfl⟩
            have hprefix := rawArithmeticPrefixStackTrace_length_le_frob
              (rawPolyMulActivationTrace x x) mstack hmstack
            have hbound := rawPolyMulActivationTrace_length_le_charge x x
            simp only [List.length_cons]
            omega
        · simp only [List.mem_map] at hreduceStack
          rcases hreduceStack with ⟨rstack, hrstack, rfl⟩
          have hprefix := rawArithmeticPrefixStackTrace_length_le_frob
            (rawReduceFuelActivationTrace modulus (Nat.log2 modulus)
              (Nat.log2 square.1 + 1) square.1) rstack hrstack
          simp only [List.length_cons]
          dsimp [square, rem] at hprefix hreduce
          omega
      · simp only [List.mem_map] at hchildStack
        rcases hchildStack with ⟨cstack, hcstack, rfl⟩
        have hchildBound := ih rem.1 cstack hcstack
        simp only [List.length_cons]
        dsimp [square, rem] at hchildBound
        omega

/-- The explicit live-bit measure for every nested Frobenius snapshot is
bounded by its composed declared frame charge and the proved per-frame
register-width envelope. -/
theorem rawCandidateFrobeniusNestedStackTrace_live_bits_le_charge
    {modulus d x W : Nat} (hmod : 1 < modulus)
    (hmodWidth : modulus < 2 ^ W) (hW : 0 < W) (hd : d ≤ W)
    (hx : x < 2 ^ W) :
    ∀ stack ∈ rawCandidateFrobeniusNestedStackTrace modulus d x,
      rawArithmeticStackLiveBits stack ≤
        rawCandidateFrobeniusNestedCharge modulus d x *
          (3 + 6 * (rawArithmeticParameterWidth (2 * W) + 1)) := by
  intro stack hstack
  apply rawArithmeticStackLiveBits_le
    (F := rawCandidateFrobeniusNestedCharge modulus d x)
    (W := rawArithmeticParameterWidth (2 * W))
  · exact rawCandidateFrobeniusNestedStackTrace_length_le_charge
      modulus d x stack hstack
  · intro frame hframe word hword
    exact rawCandidateFrobeniusNestedStackTrace_registers_lt
      hmod hmodWidth hW hd hx stack hstack frame hframe word hword

end CorruptedFieldRecovery
