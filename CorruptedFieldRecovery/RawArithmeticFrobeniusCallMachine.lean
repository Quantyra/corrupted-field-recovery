import CorruptedFieldRecovery.RawArithmeticFrobeniusNestedCostBridge

/-! A small abstract call-tree machine for the repeated-square Frobenius
routine. Its states name the active high-level phase and the explicit register
stack. The transition constructors model the source-level call sites; they do
not model Lean code generation, allocation, garbage collection, or machine
instructions. -/

namespace CorruptedFieldRecovery

inductive RawArithmeticCallPhase
  | frobenius
  | multiply
  | reduce
  deriving DecidableEq, Repr

structure RawArithmeticCallState where
  phase : RawArithmeticCallPhase
  stack : RawArithmeticStack

/-- Reachability in the abstract recursive-call tree. A Frobenius parent
remains live while the multiplier or reducer runs, and while the child
Frobenius call runs. -/
inductive RawCandidateFrobeniusCallReachable (modulus : Nat) :
    Nat → Nat → RawArithmeticCallState → Prop where
  | base (x : Nat) :
      RawCandidateFrobeniusCallReachable modulus 0 x
        ⟨.frobenius, [rawArithmeticFrobeniusFrame modulus 0 x x 0]⟩
  | parent (d x : Nat) :
      RawCandidateFrobeniusCallReachable modulus (d + 1) x
        ⟨.frobenius,
          [rawArithmeticFrobeniusFrame modulus (d + 1) x
            (rawPolyMulBitCosted x x).1
            (rawPolynomialRemainderBitCosted
              (rawPolyMulBitCosted x x).1 modulus).1]⟩
  | multiplyPrefix (d x : Nat) (stack : RawArithmeticStack)
      (hstack : stack ∈ rawArithmeticPrefixStackTrace
        (rawPolyMulActivationTrace x x)) :
      RawCandidateFrobeniusCallReachable modulus (d + 1) x
        ⟨.multiply,
          rawArithmeticFrobeniusFrame modulus (d + 1) x
            (rawPolyMulBitCosted x x).1
            (rawPolynomialRemainderBitCosted
              (rawPolyMulBitCosted x x).1 modulus).1 :: stack⟩
  | reducePrefix (d x : Nat) (stack : RawArithmeticStack)
      (hstack : stack ∈ rawArithmeticPrefixStackTrace
        (rawReduceFuelActivationTrace modulus (Nat.log2 modulus)
          (Nat.log2 (rawPolyMulBitCosted x x).1 + 1)
          (rawPolyMulBitCosted x x).1)) :
      RawCandidateFrobeniusCallReachable modulus (d + 1) x
        ⟨.reduce,
          rawArithmeticFrobeniusFrame modulus (d + 1) x
            (rawPolyMulBitCosted x x).1
            (rawPolynomialRemainderBitCosted
              (rawPolyMulBitCosted x x).1 modulus).1 :: stack⟩
  | child (d x : Nat) (state : RawArithmeticCallState)
      (hstate : RawCandidateFrobeniusCallReachable modulus d
        (rawPolynomialRemainderBitCosted
          (rawPolyMulBitCosted x x).1 modulus).1 state) :
      RawCandidateFrobeniusCallReachable modulus (d + 1) x
        ⟨state.phase,
          rawArithmeticFrobeniusFrame modulus (d + 1) x
            (rawPolyMulBitCosted x x).1
            (rawPolynomialRemainderBitCosted
              (rawPolyMulBitCosted x x).1 modulus).1 :: state.stack⟩

/-- Every generated nested-trace snapshot is a reachable state of the
source-level abstract call tree. -/
theorem rawCandidateFrobeniusNestedStackTrace_mem_call_reachable
    (modulus d x : Nat) :
    ∀ stack ∈ rawCandidateFrobeniusNestedStackTrace modulus d x,
      ∃ phase, RawCandidateFrobeniusCallReachable modulus d x
        ⟨phase, stack⟩ := by
  induction d generalizing x with
  | zero =>
      intro stack hstack
      simp only [rawCandidateFrobeniusNestedStackTrace,
        List.mem_singleton] at hstack
      subst stack
      exact ⟨.frobenius, RawCandidateFrobeniusCallReachable.base x⟩
  | succ d ih =>
      let parent := rawArithmeticFrobeniusFrame modulus (d + 1) x
        (rawPolyMulBitCosted x x).1
        (rawPolynomialRemainderBitCosted
          (rawPolyMulBitCosted x x).1 modulus).1
      intro stack hstack
      simp only [rawCandidateFrobeniusNestedStackTrace] at hstack
      rw [List.mem_append] at hstack
      rcases hstack with hleft | hchildStack
      · rw [List.mem_append] at hleft
        rcases hleft with hleft | hreduceStack
        · rw [List.mem_append] at hleft
          rcases hleft with hroot | hmulStack
          · simp only [List.mem_singleton] at hroot
            subst stack
            exact ⟨.frobenius, RawCandidateFrobeniusCallReachable.parent d x⟩
          · simp only [List.mem_map] at hmulStack
            rcases hmulStack with ⟨mstack, hmstack, rfl⟩
            exact ⟨.multiply,
              RawCandidateFrobeniusCallReachable.multiplyPrefix
                (d := d) (x := x) mstack hmstack⟩
        · simp only [List.mem_map] at hreduceStack
          rcases hreduceStack with ⟨rstack, hrstack, rfl⟩
          exact ⟨.reduce,
            RawCandidateFrobeniusCallReachable.reducePrefix
              (d := d) (x := x) rstack hrstack⟩
      · simp only [List.mem_map] at hchildStack
        rcases hchildStack with ⟨cstack, hcstack, rfl⟩
        obtain ⟨phase, hchild⟩ := ih
          (rawPolynomialRemainderBitCosted
            (rawPolyMulBitCosted x x).1 modulus).1 cstack hcstack
        exact ⟨phase, RawCandidateFrobeniusCallReachable.child
          (d := d) (x := x) ⟨phase, cstack⟩ hchild⟩

/-- Conversely, the abstract call-tree rules generate no snapshots outside
the exact composed nested trace. -/
theorem rawCandidateFrobeniusCallReachable_stack_mem_trace
    {modulus d x : Nat} {state : RawArithmeticCallState}
    (hstate : RawCandidateFrobeniusCallReachable modulus d x state) :
    state.stack ∈ rawCandidateFrobeniusNestedStackTrace modulus d x := by
  induction hstate with
  | base x => simp [rawCandidateFrobeniusNestedStackTrace]
  | parent d x =>
      simp only [rawCandidateFrobeniusNestedStackTrace, List.mem_append,
        List.mem_singleton]
      exact Or.inl (Or.inl (Or.inl trivial))
  | multiplyPrefix d x stack hstack =>
      simp only [rawCandidateFrobeniusNestedStackTrace, List.mem_append,
        List.mem_map, List.mem_singleton]
      exact Or.inl (Or.inl (Or.inr ⟨stack, hstack, rfl⟩))
  | reducePrefix d x stack hstack =>
      simp only [rawCandidateFrobeniusNestedStackTrace, List.mem_append,
        List.mem_map, List.mem_singleton]
      exact Or.inl (Or.inr ⟨stack, hstack, rfl⟩)
  | child d x state hstate ih =>
      simp only [rawCandidateFrobeniusNestedStackTrace, List.mem_append,
        List.mem_map]
      exact Or.inr ⟨state.stack, ih, rfl⟩

/-- Exact phase-erased refinement: the stacks reachable in the abstract
call-tree machine are precisely the nested-trace snapshots. -/
theorem rawCandidateFrobeniusCallReachable_iff_trace
    (modulus d x : Nat) (stack : RawArithmeticStack) :
    (∃ phase, RawCandidateFrobeniusCallReachable modulus d x
      ⟨phase, stack⟩) ↔
      stack ∈ rawCandidateFrobeniusNestedStackTrace modulus d x := by
  constructor
  · rintro ⟨phase, hstate⟩
    exact rawCandidateFrobeniusCallReachable_stack_mem_trace hstate
  · intro hstack
    obtain ⟨phase, hstate⟩ :=
      rawCandidateFrobeniusNestedStackTrace_mem_call_reachable modulus d x
        stack hstack
    exact ⟨phase, hstate⟩

/-- Reachable call-machine states inherit the proved abstract register depth
bound from the costed Frobenius computation. -/
theorem rawCandidateFrobeniusCallReachable_depth_le_declared_cost
    {modulus d x : Nat} (hmod : 1 < modulus)
    {state : RawArithmeticCallState}
    (hstate : RawCandidateFrobeniusCallReachable modulus d x state) :
    state.stack.length ≤ (rawCandidateFrobeniusAuxBitCosted modulus d x).2 + 1 := by
  exact rawCandidateFrobeniusNestedStackTrace_depth_le_declared_cost hmod
    state.stack (rawCandidateFrobeniusCallReachable_stack_mem_trace hstate)

/-- Reachable call-machine states inherit the explicit modeled live-bit bound.
This theorem is about the abstract call tree only. -/
theorem rawCandidateFrobeniusCallReachable_live_bits_le_declared_cost
    {modulus d x W : Nat} (hmod : 1 < modulus)
    (hmodWidth : modulus < 2 ^ W) (hW : 0 < W) (hd : d ≤ W)
    (hx : x < 2 ^ W) {state : RawArithmeticCallState}
    (hstate : RawCandidateFrobeniusCallReachable modulus d x state) :
    rawArithmeticStackLiveBits state.stack ≤
      ((rawCandidateFrobeniusAuxBitCosted modulus d x).2 + 1) *
        (3 + 6 * (rawArithmeticParameterWidth (2 * W) + 1)) := by
  exact rawCandidateFrobeniusNestedStackTrace_live_bits_le_declared_cost
    hmod hmodWidth hW hd hx state.stack
    (rawCandidateFrobeniusCallReachable_stack_mem_trace hstate)

end CorruptedFieldRecovery
