import CorruptedFieldRecovery.RawArithmeticFrobeniusCallMachine

/-! An ordered, phase-labelled schedule for the abstract Frobenius call tree.
The schedule orders parent, multiplier-prefix, reducer-prefix, and recursive
child events. These are source-level call snapshots, not individual bit
operations or a Lean runtime trace. -/

namespace CorruptedFieldRecovery

/-- Ordered phase events for the source-level abstract recursive call run. -/
def rawCandidateFrobeniusCallRun (modulus : Nat) : Nat → Nat →
    List RawArithmeticCallState
  | 0, x =>
      [⟨.frobenius, [rawArithmeticFrobeniusFrame modulus 0 x x 0]⟩]
  | d + 1, x =>
      let square := rawPolyMulBitCosted x x
      let rem := rawPolynomialRemainderBitCosted square.1 modulus
      let parent := rawArithmeticFrobeniusFrame modulus (d + 1) x
        square.1 rem.1
      [⟨.frobenius, [parent]⟩] ++
        (rawArithmeticPrefixStackTrace (rawPolyMulActivationTrace x x)).map
          (fun stack => ⟨.multiply, parent :: stack⟩) ++
        (rawArithmeticPrefixStackTrace
          (rawReduceFuelActivationTrace modulus (Nat.log2 modulus)
            (Nat.log2 square.1 + 1) square.1)).map
          (fun stack => ⟨.reduce, parent :: stack⟩) ++
        (rawCandidateFrobeniusCallRun modulus d rem.1).map
          (fun state => ⟨state.phase, parent :: state.stack⟩)
termination_by d _ => d
decreasing_by omega

/-- Erasing phase labels from the ordered event schedule gives exactly the
previously audited composed snapshot list. -/
theorem rawCandidateFrobeniusCallRun_map_stack_eq_nestedTrace
    (modulus d x : Nat) :
    (rawCandidateFrobeniusCallRun modulus d x).map
      RawArithmeticCallState.stack =
        rawCandidateFrobeniusNestedStackTrace modulus d x := by
  induction d generalizing x with
  | zero => simp [rawCandidateFrobeniusCallRun,
      rawCandidateFrobeniusNestedStackTrace]
  | succ d ih =>
      let rem := rawPolynomialRemainderBitCosted
        (rawPolyMulBitCosted x x).1 modulus
      let parent := rawArithmeticFrobeniusFrame modulus (d + 1) x
        (rawPolyMulBitCosted x x).1 rem.1
      have hchild :
          (rawCandidateFrobeniusCallRun modulus d rem.1).map
            (fun state => parent :: state.stack) =
          (rawCandidateFrobeniusNestedStackTrace modulus d rem.1).map
            (fun stack => parent :: stack) := by
        have h := congrArg
          (List.map (fun stack => parent :: stack)) (ih rem.1)
        simpa only [List.map_map, Function.comp_def] using h
      dsimp [parent, rem] at hchild
      simp only [rawCandidateFrobeniusCallRun,
        rawCandidateFrobeniusNestedStackTrace, List.map_append,
        List.map_map, Function.comp_def]
      rw [hchild]
      simp only [List.map_cons, List.map_nil]

/-- Each event in the ordered schedule refines to a state in the accepted
abstract call-tree reachability relation. -/
theorem rawCandidateFrobeniusCallRun_mem_reachable_exact
    (modulus d x : Nat) {state : RawArithmeticCallState}
    (hstate : state ∈ rawCandidateFrobeniusCallRun modulus d x) :
    RawCandidateFrobeniusCallReachable modulus d x state := by
  induction d generalizing x state with
  | zero =>
      simp only [rawCandidateFrobeniusCallRun, List.mem_singleton] at hstate
      subst state
      exact RawCandidateFrobeniusCallReachable.base x
  | succ d ih =>
      let rem := rawPolynomialRemainderBitCosted
        (rawPolyMulBitCosted x x).1 modulus
      simp only [rawCandidateFrobeniusCallRun, List.mem_append] at hstate
      rcases hstate with hbeforeChild | hchild
      · rcases hbeforeChild with hbeforeReduce | hreduce
        · rcases hbeforeReduce with hroot | hmul
          · simp only [List.mem_singleton] at hroot
            subst state
            exact RawCandidateFrobeniusCallReachable.parent d x
          · simp only [List.mem_map] at hmul
            rcases hmul with ⟨stack, hstack, rfl⟩
            exact RawCandidateFrobeniusCallReachable.multiplyPrefix
              d x stack hstack
        · simp only [List.mem_map] at hreduce
          rcases hreduce with ⟨stack, hstack, rfl⟩
          exact RawCandidateFrobeniusCallReachable.reducePrefix
            d x stack hstack
      · simp only [List.mem_map] at hchild
        rcases hchild with ⟨childState, hchild, rfl⟩
        exact RawCandidateFrobeniusCallReachable.child d x childState
          (ih rem.1 hchild)

theorem rawCandidateFrobeniusCallRun_mem_reachable
    (modulus d x : Nat) {state : RawArithmeticCallState}
    (hstate : state ∈ rawCandidateFrobeniusCallRun modulus d x) :
    ∃ phase, RawCandidateFrobeniusCallReachable modulus d x
      ⟨phase, state.stack⟩ := by
  exact ⟨state.phase,
    rawCandidateFrobeniusCallRun_mem_reachable_exact modulus d x hstate⟩

/-- Ordered abstract run events inherit the declared-cost stack-depth bound.
This is call-event depth, not machine instruction count. -/
theorem rawCandidateFrobeniusCallRun_depth_le_declared_cost
    {modulus d x : Nat} (hmod : 1 < modulus)
    {state : RawArithmeticCallState}
    (hstate : state ∈ rawCandidateFrobeniusCallRun modulus d x) :
    state.stack.length ≤ (rawCandidateFrobeniusAuxBitCosted modulus d x).2 + 1 := by
  obtain ⟨phase, hreachable⟩ :=
    rawCandidateFrobeniusCallRun_mem_reachable modulus d x hstate
  have htrace := rawCandidateFrobeniusCallReachable_stack_mem_trace hreachable
  exact rawCandidateFrobeniusNestedStackTrace_depth_le_declared_cost hmod
    state.stack htrace

end CorruptedFieldRecovery
