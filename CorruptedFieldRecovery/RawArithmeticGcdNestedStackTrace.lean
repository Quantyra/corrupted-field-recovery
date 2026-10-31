import CorruptedFieldRecovery.RawArithmeticTraceSpaceBounds
import CorruptedFieldRecovery.RawArithmeticReduceTraceWidth

/-! A nested explicit stack trace for the costed Euclidean GCD. While each
GCD activation computes its actual remainder, the parent GCD frame is retained
around the reducer's recursive activation prefixes; it is then retained around
the recursive GCD child. This remains the declared register-stack model, not
Lean evaluator stack or heap usage. -/

namespace CorruptedFieldRecovery

/-- Prefix-stack snapshots of a recursive frame path. -/
def rawArithmeticPrefixStackTrace : RawArithmeticStack → List RawArithmeticStack
  | [] => []
  | frame :: tail => [[frame]] ++
      (rawArithmeticPrefixStackTrace tail).map (fun stack => frame :: stack)

private theorem rawArithmeticPrefixStackTrace_length_le
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

private theorem rawArithmeticPrefixStackTrace_frames_mem
    (frames : RawArithmeticStack) :
    ∀ stack ∈ rawArithmeticPrefixStackTrace frames,
      ∀ frame ∈ stack, frame ∈ frames := by
  induction frames with
  | nil => simp [rawArithmeticPrefixStackTrace]
  | cons head tail ih =>
      intro stack hstack frame hframe
      simp only [rawArithmeticPrefixStackTrace, List.mem_append,
        List.mem_singleton, List.mem_map] at hstack
      rcases hstack with hhead | ⟨tailStack, htail, rfl⟩
      · subst stack
        simp only [List.mem_singleton] at hframe
        subst frame
        simp
      · simp only [List.mem_cons] at hframe
        rcases hframe with heq | hframe
        · subst frame
          simp
        · exact List.mem_cons_of_mem head (ih tailStack htail frame hframe)

private theorem rawPolynomialGcdBitCostedFrames_pos (a b : Nat) :
    0 < rawPolynomialGcdBitCostedFrames a b := by
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
      cases b with
      | zero => simp [rawPolynomialGcdBitCostedFrames]
      | succ b =>
          cases b with
          | zero => simp [rawPolynomialGcdBitCostedFrames]
          | succ b =>
              simp only [rawPolynomialGcdBitCostedFrames]
              omega

/-- In a GCD step with divisor above one, the costed remainder's returned
mask is exactly the bounded reducer output whose activation path is nested
under the parent GCD frame. -/
theorem rawPolynomialGcdRemainderUsesReducer
    {dividend divisor : Nat} (hdivisor : 1 < divisor) :
    (rawPolynomialRemainderBitCosted dividend divisor).1 =
      (rawReduceFuelBitCosted divisor (Nat.log2 divisor)
        (Nat.log2 dividend + 1) dividend).1 := by
  have hzero : divisor ≠ 0 := by omega
  have hone : divisor ≠ 1 := by omega
  simp [rawPolynomialRemainderBitCosted, hzero, hone]

/-- Nested activation-stack snapshots for the actual costed GCD. -/
def rawPolynomialGcdNestedStackTrace : Nat → Nat → List RawArithmeticStack
  | a, 0 => [[rawArithmeticGcdActivationFrame a 0 0 a]]
  | a, 1 => [[rawArithmeticGcdActivationFrame a 1 0 1]]
  | a, b + 2 =>
      let rem := rawPolynomialRemainderBitCosted a (b + 2)
      let rest := rawPolynomialGcdBitCosted (b + 2) rem.1
      let parent := rawArithmeticGcdActivationFrame a (b + 2) rem.1 rest.1
      let reducerTrace := rawReduceFuelActivationTrace (b + 2)
        (Nat.log2 (b + 2)) (Nat.log2 a + 1) a
      ([[parent]] ++
        (rawArithmeticPrefixStackTrace reducerTrace).map
          (fun stack => parent :: stack)) ++
        (rawPolynomialGcdNestedStackTrace (b + 2) rem.1).map
          (fun stack => parent :: stack)
termination_by _ b => b
decreasing_by
  rw [rawPolynomialRemainderBitCosted_fst]
  exact rawPolynomialRemainder_lt (by omega)

/-- Every register in every nested GCD/remainder activation stack remains
within the W-bit parameter envelope when the original inputs are W-bit. -/
theorem rawPolynomialGcdNestedStackTrace_registers_lt
    {a b W : Nat} (hW : 0 < W) (ha : a < 2 ^ W) (hb : b < 2 ^ W) :
    ∀ stack ∈ rawPolynomialGcdNestedStackTrace a b,
      ∀ frame ∈ stack, ∀ word ∈ frame.registers,
        word < 2 ^ rawArithmeticParameterWidth W := by
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
      cases b with
      | zero =>
          intro stack hstack frame hframe word hword
          simp only [rawPolynomialGcdNestedStackTrace, List.mem_singleton] at hstack
          subst stack
          simp only [List.mem_singleton] at hframe
          subst frame
          have hparent : rawArithmeticGcdActivationFrame a 0 0 a ∈
              rawPolynomialGcdActivationTrace a 0 := by simp [rawPolynomialGcdActivationTrace]
          exact rawPolynomialGcdActivationTrace_registers_lt hW ha
            (Nat.pow_pos (by decide : 0 < (2 : Nat))) _ hparent word hword
      | succ b =>
          cases b with
          | zero =>
              intro stack hstack frame hframe word hword
              simp only [Nat.zero_add] at hstack
              simp only [rawPolynomialGcdNestedStackTrace, List.mem_singleton] at hstack
              subst stack
              simp only [List.mem_singleton] at hframe
              subst frame
              have hparent : rawArithmeticGcdActivationFrame a 1 0 1 ∈
                  rawPolynomialGcdActivationTrace a 1 := by
                simp [rawPolynomialGcdActivationTrace]
              exact rawPolynomialGcdActivationTrace_registers_lt hW ha hb
                _ hparent word hword
          | succ b =>
              let rem := rawPolynomialRemainderBitCosted a (b + 2)
              let rest := rawPolynomialGcdBitCosted (b + 2) rem.1
              let parent := rawArithmeticGcdActivationFrame a (b + 2) rem.1 rest.1
              let reducerTrace := rawReduceFuelActivationTrace (b + 2)
                (Nat.log2 (b + 2)) (Nat.log2 a + 1) a
              have hrem : rem.1 < b + 2 := by
                rw [rawPolynomialRemainderBitCosted_fst]
                exact rawPolynomialRemainder_lt (by omega)
              have hremWidth : rem.1 < 2 ^ W := lt_trans hrem hb
              have hparent : ∀ word ∈ parent.registers,
                  word < 2 ^ rawArithmeticParameterWidth W := by
                dsimp [parent]
                exact rawPolynomialGcdActivationTrace_registers_lt hW ha hb
                  (rawArithmeticGcdActivationFrame a (b + 2) rem.1 rest.1)
                  (by
                    dsimp [rem, rest]
                    simp [rawPolynomialGcdActivationTrace])
              have hdivisorZero : b + 2 ≠ 0 := by omega
              have hmodLower : 2 ^ Nat.log2 (b + 2) ≤ b + 2 :=
                Nat.log2_self_le hdivisorZero
              have hmodUpper : b + 2 < 2 ^ (Nat.log2 (b + 2) + 1) :=
                Nat.lt_log2_self
              have hdegree : Nat.log2 (b + 2) < W :=
                rawLog2_lt_of_lt_pow hW hb
              have hfuel : Nat.log2 a + 1 ≤ W := by
                have hlog := rawLog2_lt_of_lt_pow hW ha
                omega
              have hreduce : ∀ rframe ∈ reducerTrace,
                  ∀ rword ∈ rframe.registers,
                    rword < 2 ^ rawArithmeticParameterWidth W := by
                dsimp [reducerTrace]
                exact rawReduceFuelActivationTrace_registers_lt hmodLower
                  hmodUpper hdegree hW hfuel ha
              have hchild := ih rem.1 hrem (a := b + 2) hb hremWidth
              intro stack hstack frame hframe word hword
              simp only [rawPolynomialGcdNestedStackTrace] at hstack
              rw [List.mem_append] at hstack
              rcases hstack with hleft | hchildStack
              · rw [List.mem_append] at hleft
                rcases hleft with hroot | hreduceStack
                · simp only [List.mem_singleton] at hroot
                  subst stack
                  simp only [List.mem_singleton] at hframe
                  subst frame
                  exact hparent word hword
                · simp only [List.mem_map] at hreduceStack
                  rcases hreduceStack with ⟨rstack, hrprefix, heq⟩
                  subst stack
                  simp only [List.mem_cons] at hframe
                  rcases hframe with hrootFrame | hreduceFrame
                  · subst frame
                    exact hparent word hword
                  · have hsource :=
                      rawArithmeticPrefixStackTrace_frames_mem reducerTrace rstack
                        hrprefix frame hreduceFrame
                    exact hreduce frame hsource word hword
              · simp only [List.mem_map] at hchildStack
                rcases hchildStack with ⟨cstack, hcstack, heq⟩
                subst stack
                simp only [List.mem_cons] at hframe
                rcases hframe with hrootFrame | hchildFrame
                · subst frame
                  exact hparent word hword
                · exact hchild cstack hcstack frame hchildFrame word hword

/-- Every nested GCD/remainder stack has at most one parent GCD frame plus the
reducer's fuel-many active frames or the recursive child's stack. -/
theorem rawPolynomialGcdNestedStackTrace_length_le
    {a b W : Nat} (hW : 0 < W) (ha : a < 2 ^ W) (hb : b < 2 ^ W) :
    ∀ stack ∈ rawPolynomialGcdNestedStackTrace a b,
      stack.length ≤ rawPolynomialGcdBitCostedFrames a b * (W + 2) := by
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
      cases b with
      | zero =>
          intro stack hstack
          simp only [rawPolynomialGcdNestedStackTrace, List.mem_singleton] at hstack
          subst stack
          simp [rawPolynomialGcdBitCostedFrames]
      | succ b =>
          cases b with
          | zero =>
              intro stack hstack
              simp only [Nat.zero_add] at hstack
              simp only [rawPolynomialGcdNestedStackTrace, List.mem_singleton] at hstack
              subst stack
              simp [rawPolynomialGcdBitCostedFrames]
          | succ b =>
              let rem := rawPolynomialRemainderBitCosted a (b + 2)
              let rest := rawPolynomialGcdBitCosted (b + 2) rem.1
              let parent := rawArithmeticGcdActivationFrame a (b + 2) rem.1 rest.1
              let reducerTrace := rawReduceFuelActivationTrace (b + 2)
                (Nat.log2 (b + 2)) (Nat.log2 a + 1) a
              have hrem : rem.1 < b + 2 := by
                rw [rawPolynomialRemainderBitCosted_fst]
                exact rawPolynomialRemainder_lt (by omega)
              have hfuel : Nat.log2 a + 1 ≤ W := by
                have hlog := rawLog2_lt_of_lt_pow hW ha
                omega
              have hredLen := rawReduceFuelActivationTrace_length_le
                (b + 2) (Nat.log2 (b + 2)) (Nat.log2 a + 1) a
              have hprefix : ∀ stack ∈ rawArithmeticPrefixStackTrace reducerTrace,
                  stack.length ≤ Nat.log2 a + 2 := by
                intro stack hstack
                have hp := rawArithmeticPrefixStackTrace_length_le reducerTrace stack hstack
                have hr := hredLen
                dsimp [reducerTrace] at hp
                omega
              have hremWidth : rem.1 < 2 ^ W := lt_trans hrem hb
              have hchild := ih rem.1 hrem (a := b + 2) hb hremWidth
              have hchildFrames :
                  1 ≤ rawPolynomialGcdBitCostedFrames (b + 2) rem.1 :=
                Nat.succ_le_of_lt (rawPolynomialGcdBitCostedFrames_pos (b + 2) rem.1)
              have hlarge : W + 2 ≤
                  (1 + rawPolynomialGcdBitCostedFrames (b + 2) rem.1) * (W + 2) := by
                have hbase : W + 2 ≤
                    rawPolynomialGcdBitCostedFrames (b + 2) rem.1 * (W + 2) := by
                  have hm := Nat.mul_le_mul_right (W + 2) hchildFrames
                  simpa using hm
                have hstep : rawPolynomialGcdBitCostedFrames (b + 2) rem.1 * (W + 2) ≤
                    (1 + rawPolynomialGcdBitCostedFrames (b + 2) rem.1) * (W + 2) := by
                  exact Nat.mul_le_mul_right (W + 2) (Nat.le_add_left _ _)
                exact le_trans hbase hstep
              intro stack hstack
              simp only [rawPolynomialGcdNestedStackTrace] at hstack
              rw [List.mem_append] at hstack
              rcases hstack with hleft | hchildStack
              · rw [List.mem_append] at hleft
                rcases hleft with hroot | hreduceStack
                · simp only [List.mem_singleton] at hroot
                  subst stack
                  simp only [List.length_singleton, rawPolynomialGcdBitCostedFrames]
                  dsimp [rem] at hlarge
                  omega
                · simp only [List.mem_map] at hreduceStack
                  rcases hreduceStack with ⟨rstack, hrprefix, heq⟩
                  subst stack
                  have hp := hprefix rstack hrprefix
                  simp only [List.length_cons]
                  simp only [rawPolynomialGcdBitCostedFrames]
                  dsimp [rem] at hlarge
                  omega
              · simp only [List.mem_map] at hchildStack
                rcases hchildStack with ⟨cstack, hcstack, heq⟩
                subst stack
                have hc := hchild cstack hcstack
                dsimp [rem] at hc
                simp only [List.length_cons, rawPolynomialGcdBitCostedFrames]
                nlinarith

/-- The nested GCD/remainder path has an explicit abstract live-bit bound from
its proved maximum stack depth and the reachable-register width invariant. -/
theorem rawPolynomialGcdNestedStackTrace_live_bits_le
    {a b W : Nat} (hW : 0 < W) (ha : a < 2 ^ W) (hb : b < 2 ^ W) :
    ∀ stack ∈ rawPolynomialGcdNestedStackTrace a b,
      rawArithmeticStackLiveBits stack ≤
        (rawPolynomialGcdBitCostedFrames a b * (W + 2)) *
          (3 + 6 * (rawArithmeticParameterWidth W + 1)) := by
  intro stack hstack
  apply rawArithmeticStackLiveBits_le
    (stack := stack)
    (F := rawPolynomialGcdBitCostedFrames a b * (W + 2))
    (W := rawArithmeticParameterWidth W)
  · exact rawPolynomialGcdNestedStackTrace_length_le hW ha hb stack hstack
  · intro frame hframe word hword
    exact rawPolynomialGcdNestedStackTrace_registers_lt hW ha hb
      stack hstack frame hframe word hword

end CorruptedFieldRecovery
