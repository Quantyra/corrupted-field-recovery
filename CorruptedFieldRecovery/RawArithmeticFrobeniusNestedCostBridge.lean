import CorruptedFieldRecovery.RawArithmeticFrobeniusNestedStackTrace
import CorruptedFieldRecovery.RawRabinFrobeniusBitCost

/-! Relate the composed Frobenius register snapshots to the existing declared
Frobenius operation charge. The result concerns the explicit trace model; it
does not assert Lean evaluator runtime, reachability, or heap usage. -/

namespace CorruptedFieldRecovery

private theorem rawArithmeticPrefixStackTrace_length_le_bridge
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

private theorem rawReduceFuelActivationTrace_length_le_cost_add_one
    (modulus degree fuel a : Nat) :
    (rawReduceFuelActivationTrace modulus degree fuel a).length ≤
      (rawReduceFuelBitCosted modulus degree fuel a).2 + 1 := by
  induction fuel generalizing a with
  | zero => simp [rawReduceFuelActivationTrace, rawReduceFuelBitCosted]
  | succ fuel ih =>
      by_cases hsmall : a < 2 ^ degree
      · simp [rawReduceFuelActivationTrace, rawReduceFuelBitCosted, hsmall]
      · let step := rawReduceStepBitCosted modulus degree a
        simp only [rawReduceFuelActivationTrace, if_neg hsmall,
          List.length_cons]
        have htail := ih step.1
        simp only [rawReduceFuelBitCosted, if_neg hsmall]
        have hcompare : 1 ≤ rawNatBitWidth a + degree + 1 := by omega
        dsimp [step] at htail ⊢
        omega

private theorem rawNatBitWidth_ge_one_bridge (n : Nat) :
    1 ≤ rawNatBitWidth n := by
  unfold rawNatBitWidth
  omega

/-- Each explicit nested Frobenius stack snapshot has depth at most the
declared cost of the exact costed repeated-square computation, plus one base
frame. Reduction prefixes are charged by the reducer's actual costed call,
not by its maximum fuel allowance. -/
theorem rawCandidateFrobeniusNestedStackTrace_depth_le_declared_cost
    {modulus d x : Nat} (hmod : 1 < modulus) :
    ∀ stack ∈ rawCandidateFrobeniusNestedStackTrace modulus d x,
      stack.length ≤ (rawCandidateFrobeniusAuxBitCosted modulus d x).2 + 1 := by
  induction d generalizing x with
  | zero =>
      intro stack hstack
      simp only [rawCandidateFrobeniusNestedStackTrace,
        List.mem_singleton] at hstack
      subst stack
      simp [rawCandidateFrobeniusAuxBitCosted]
  | succ d ih =>
      let square := rawPolyMulBitCosted x x
      let rem := rawPolynomialRemainderBitCosted square.1 modulus
      let mulTrace := rawPolyMulActivationTrace x x
      let reduceTrace := rawReduceFuelActivationTrace modulus
        (Nat.log2 modulus) (Nat.log2 square.1 + 1) square.1
      have hcost : (rawCandidateFrobeniusAuxBitCosted modulus (d + 1) x).2 =
          square.2 + rem.2 + rawNatBitWidth modulus +
            rawNatBitWidth x +
            (rawCandidateFrobeniusAuxBitCosted modulus d rem.1).2 := by
        simp only [rawCandidateFrobeniusAuxBitCosted]
        dsimp [square, rem]
      have hwidthMod := rawNatBitWidth_ge_one_bridge modulus
      have hwidthX := rawNatBitWidth_ge_one_bridge x
      have hmul := rawPolyMulActivationTrace_length_le_charge x x
      have hreduce := rawReduceFuelActivationTrace_length_le_cost_add_one
        modulus (Nat.log2 modulus) (Nat.log2 square.1 + 1) square.1
      have hremCost : rem.2 =
          (rawReduceFuelBitCosted modulus (Nat.log2 modulus)
            (Nat.log2 square.1 + 1) square.1).2 := by
        have hzero : modulus ≠ 0 := by omega
        have hone : modulus ≠ 1 := by omega
        simp [rem, rawPolynomialRemainderBitCosted, hzero, hone]
      dsimp [square, rem] at hmul hreduce hremCost hcost
      intro stack hstack
      simp only [rawCandidateFrobeniusNestedStackTrace] at hstack
      rw [List.mem_append] at hstack
      rw [hcost]
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
            have hprefix := rawArithmeticPrefixStackTrace_length_le_bridge
              (rawPolyMulActivationTrace x x) mstack hmstack
            simp only [List.length_cons]
            omega
        · simp only [List.mem_map] at hreduceStack
          rcases hreduceStack with ⟨rstack, hrstack, rfl⟩
          have hprefix := rawArithmeticPrefixStackTrace_length_le_bridge
            (rawReduceFuelActivationTrace modulus (Nat.log2 modulus)
              (Nat.log2 square.1 + 1) square.1) rstack hrstack
          simp only [List.length_cons] at hprefix ⊢
          dsimp [square, rem] at hprefix hreduce hremCost
          omega
      · simp only [List.mem_map] at hchildStack
        rcases hchildStack with ⟨cstack, hcstack, rfl⟩
        have hchild := ih (x := rem.1) cstack hcstack
        simp only [List.length_cons]
        dsimp [square, rem] at hchild hcost
        omega

/-- For the composed abstract nested trace, live register bits are bounded by
the declared repeated-square Frobenius cost plus one base frame, times the
proved per-frame width allowance. -/
theorem rawCandidateFrobeniusNestedStackTrace_live_bits_le_declared_cost
    {modulus d x W : Nat} (hmod : 1 < modulus)
    (hmodWidth : modulus < 2 ^ W) (hW : 0 < W) (hd : d ≤ W)
    (hx : x < 2 ^ W) :
    ∀ stack ∈ rawCandidateFrobeniusNestedStackTrace modulus d x,
      rawArithmeticStackLiveBits stack ≤
        ((rawCandidateFrobeniusAuxBitCosted modulus d x).2 + 1) *
          (3 + 6 * (rawArithmeticParameterWidth (2 * W) + 1)) := by
  intro stack hstack
  apply rawArithmeticStackLiveBits_le
    (F := (rawCandidateFrobeniusAuxBitCosted modulus d x).2 + 1)
    (W := rawArithmeticParameterWidth (2 * W))
  · exact rawCandidateFrobeniusNestedStackTrace_depth_le_declared_cost
      hmod stack hstack
  · intro frame hframe word hword
    exact rawCandidateFrobeniusNestedStackTrace_registers_lt
      hmod hmodWidth hW hd hx stack hstack frame hframe word hword

end CorruptedFieldRecovery
