import CorruptedFieldRecovery.RawArithmeticGcdNestedStackTrace

/-! Compose each repeated-square Frobenius activation with the actual
recursive multiplier and reducer activation paths. The width invariant below
is for these explicit registers and prefixes only; it is not a Lean evaluator
stack or heap theorem. -/

namespace CorruptedFieldRecovery

private theorem rawArithmeticPrefixStackTrace_frames_mem_frob
    (frames : RawArithmeticStack) :
    ∀ stack ∈ rawArithmeticPrefixStackTrace frames,
      ∀ frame ∈ stack, frame ∈ frames := by
  induction frames with
  | nil => simp [rawArithmeticPrefixStackTrace]
  | cons head tail ih =>
      intro stack hstack frame hframe
      simp only [rawArithmeticPrefixStackTrace, List.mem_append,
        List.mem_singleton, List.mem_map] at hstack
      rcases hstack with hhead | ⟨tailStack, htail, heq⟩
      · subst stack
        simp only [List.mem_singleton] at hframe
        subst frame
        simp
      · subst stack
        simp only [List.mem_cons] at hframe
        rcases hframe with heqHead | hframe
        · subst frame
          simp
        · exact List.mem_cons_of_mem head (ih tailStack htail frame hframe)

private theorem rawFrobeniusNested_lt_parameter
    {n v W : Nat} (hn : n < 2 ^ v) (hv : v ≤ W) :
    n < 2 ^ rawArithmeticParameterWidth W := by
  exact lt_of_lt_of_le hn
    (Nat.pow_le_pow_right (by decide : 0 < 2) (by
      unfold rawArithmeticParameterWidth
      omega))

/-- Nested activation-stack snapshots for the actual repeated-square loop.
The current Frobenius frame surrounds multiplication, then reduction, then
the recursive Frobenius call. Prefixes record the nested call stacks. -/
def rawCandidateFrobeniusNestedStackTrace (modulus : Nat) :
    Nat → Nat → List RawArithmeticStack
  | 0, x => [[rawArithmeticFrobeniusFrame modulus 0 x x 0]]
  | d + 1, x =>
      let square := rawPolyMulBitCosted x x
      let rem := rawPolynomialRemainderBitCosted square.1 modulus
      let parent := rawArithmeticFrobeniusFrame modulus (d + 1) x square.1 rem.1
      let mulTrace := rawPolyMulActivationTrace x x
      let reduceTrace := rawReduceFuelActivationTrace modulus
        (Nat.log2 modulus) (Nat.log2 square.1 + 1) square.1
      [[parent]] ++
        (rawArithmeticPrefixStackTrace mulTrace).map
          (fun stack => parent :: stack) ++
        (rawArithmeticPrefixStackTrace reduceTrace).map
          (fun stack => parent :: stack) ++
        (rawCandidateFrobeniusNestedStackTrace modulus d rem.1).map
          (fun stack => parent :: stack)
termination_by d _ => d
decreasing_by omega

/-- Every register in the nested Frobenius/multiply/reduce snapshots fits the
parameterized envelope for a 2W-bit intermediate square. The modulus, initial
representative, and every reduced child are W-bit. -/
theorem rawCandidateFrobeniusNestedStackTrace_registers_lt
    {modulus d x W : Nat} (hmod : 1 < modulus)
    (hmodWidth : modulus < 2 ^ W) (hW : 0 < W) (hd : d ≤ W)
    (hx : x < 2 ^ W) :
    ∀ stack ∈ rawCandidateFrobeniusNestedStackTrace modulus d x,
      ∀ frame ∈ stack, ∀ word ∈ frame.registers,
        word < 2 ^ rawArithmeticParameterWidth (2 * W) := by
  have hW2 : 0 < 2 * W := by omega
  have hmodNe : modulus ≠ 0 := by omega
  have hmodWidth2 : modulus < 2 ^ (2 * W) := by
    exact lt_of_lt_of_le hmodWidth
      (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))
  induction d using Nat.strong_induction_on generalizing x with
  | h d ih =>
      cases d with
      | zero =>
          intro stack hstack frame hframe word hword
          simp only [rawCandidateFrobeniusNestedStackTrace, List.mem_singleton] at hstack
          subst stack
          simp only [List.mem_singleton] at hframe
          subst frame
          have hparent : rawArithmeticFrobeniusFrame modulus 0 x x 0 ∈
              rawCandidateFrobeniusActivationTrace modulus 0 x := by
            simp [rawCandidateFrobeniusActivationTrace]
          exact rawCandidateFrobeniusActivationTrace_registers_lt
            (modulus := modulus) (d := 0) (x := x) (W := W)
            hmodNe hmodWidth hW (by omega) hx _ hparent word hword
      | succ d =>
          have hdChild : d ≤ W := by omega
          let square := rawPolyMulBitCosted x x
          let rem := rawPolynomialRemainderBitCosted square.1 modulus
          let parent := rawArithmeticFrobeniusFrame modulus (d + 1) x square.1 rem.1
          let mulTrace := rawPolyMulActivationTrace x x
          let reduceTrace := rawReduceFuelActivationTrace modulus
            (Nat.log2 modulus) (Nat.log2 square.1 + 1) square.1
          have hSquareWidth : square.1 < 2 ^ (2 * W) := by
            rw [show square.1 = rawPolyMul x x by
              dsimp [square]
              exact rawPolyMulBitCosted_fst x x]
            simpa [two_mul] using rawPolyMul_lt_pow W W x x hx hx
          have hrem : rem.1 < 2 ^ W := by
            rw [show rem.1 = rawPolynomialRemainder square.1 modulus by
              dsimp [rem]
              exact rawPolynomialRemainderBitCosted_fst square.1 modulus]
            exact lt_trans
              (rawPolynomialRemainder_lt (by omega : modulus ≠ 0)) hmodWidth
          have hparent : ∀ word ∈ parent.registers,
              word < 2 ^ rawArithmeticParameterWidth (2 * W) := by
            dsimp [parent]
            exact rawCandidateFrobeniusActivationTrace_registers_lt
              (modulus := modulus) (d := d + 1) (x := x) (W := W)
              hmodNe hmodWidth hW (by omega) hx
              (rawArithmeticFrobeniusFrame modulus (d + 1) x square.1 rem.1)
              (by
                dsimp [square, rem]
                simp only [rawCandidateFrobeniusActivationTrace, List.mem_cons]
                exact Or.inl trivial)
          have hmul : ∀ mframe ∈ mulTrace, ∀ mword ∈ mframe.registers,
              mword < 2 ^ rawArithmeticParameterWidth (2 * W) := by
            dsimp [mulTrace]
            intro mframe hmframe mword hmword
            have hm := rawPolyMulActivationTrace_registers_lt hx hx mframe hmframe
              mword hmword
            have hmulExp : 2 * W + 1 ≤ rawArithmeticParameterWidth (2 * W) := by
              unfold rawArithmeticParameterWidth
              omega
            exact lt_of_lt_of_le hm
              (Nat.pow_le_pow_right (by decide : 0 < 2) hmulExp)
          have hmodLower : 2 ^ Nat.log2 modulus ≤ modulus :=
            Nat.log2_self_le (by omega)
          have hmodUpper : modulus < 2 ^ (Nat.log2 modulus + 1) := Nat.lt_log2_self
          have hdegree : Nat.log2 modulus < 2 * W :=
            rawLog2_lt_of_lt_pow hW2 hmodWidth2
          have hfuel : Nat.log2 square.1 + 1 ≤ 2 * W := by
            have hlog := rawLog2_lt_of_lt_pow hW2 hSquareWidth
            omega
          have hreduce : ∀ rframe ∈ reduceTrace,
              ∀ rword ∈ rframe.registers,
                rword < 2 ^ rawArithmeticParameterWidth (2 * W) := by
            dsimp [reduceTrace]
            exact rawReduceFuelActivationTrace_registers_lt
              hmodLower hmodUpper hdegree hW2 hfuel hSquareWidth
          have hchild := ih d (by omega) hdChild hrem
          intro stack hstack frame hframe word hword
          simp only [rawCandidateFrobeniusNestedStackTrace] at hstack
          rw [List.mem_append] at hstack
          rcases hstack with hleft | hchildStack
          · rw [List.mem_append] at hleft
            rcases hleft with hleft | hreduceStack
            · rw [List.mem_append] at hleft
              rcases hleft with hroot | hmulStack
              · simp only [List.mem_singleton] at hroot
                subst stack
                simp only [List.mem_singleton] at hframe
                subst frame
                exact hparent word hword
              · simp only [List.mem_map] at hmulStack
                rcases hmulStack with ⟨mstack, hmprefix, heq⟩
                subst stack
                simp only [List.mem_cons] at hframe
                rcases hframe with hrootFrame | hmulFrame
                · subst frame
                  exact hparent word hword
                · have hsrc :=
                    rawArithmeticPrefixStackTrace_frames_mem_frob mulTrace mstack
                      hmprefix frame hmulFrame
                  exact hmul frame hsrc word hword
            · simp only [List.mem_map] at hreduceStack
              rcases hreduceStack with ⟨rstack, hrprefix, heq⟩
              subst stack
              simp only [List.mem_cons] at hframe
              rcases hframe with hrootFrame | hreduceFrame
              · subst frame
                exact hparent word hword
              · have hsrc :=
                  rawArithmeticPrefixStackTrace_frames_mem_frob reduceTrace rstack
                    hrprefix frame hreduceFrame
                exact hreduce frame hsrc word hword
          · simp only [List.mem_map] at hchildStack
            rcases hchildStack with ⟨cstack, hcstack, heq⟩
            subst stack
            simp only [List.mem_cons] at hframe
            rcases hframe with hrootFrame | hchildFrame
            · subst frame
              exact hparent word hword
            · exact hchild cstack hcstack frame hchildFrame word hword

end CorruptedFieldRecovery
