import CorruptedFieldRecovery.RawPolynomialBitCost

/-! A paired list-construction recurrence for `List.range`, with explicit
cell-allocation charge and output-space bounds. -/

namespace CorruptedFieldRecovery

/-- Append one item while charging one list-cell traversal/allocation for each
existing cons cell. -/
def rawListAppendSingletonBitCosted : List Nat → Nat → List Nat × Nat
  | [], x => ([x], 0)
  | y :: ys, x =>
      let rest := rawListAppendSingletonBitCosted ys x
      (y :: rest.1, rest.2 + 1)
termination_by xs _ => xs.length
decreasing_by simp_wf

theorem rawListAppendSingletonBitCosted_fst (xs : List Nat) (x : Nat) :
    (rawListAppendSingletonBitCosted xs x).1 = xs ++ [x] := by
  induction xs with
  | nil => simp [rawListAppendSingletonBitCosted]
  | cons y ys ih => simp [rawListAppendSingletonBitCosted, ih]

theorem rawListAppendSingletonBitCosted_cost_le (xs : List Nat) (x : Nat) :
    (rawListAppendSingletonBitCosted xs x).2 ≤ xs.length := by
  induction xs with
  | nil => simp [rawListAppendSingletonBitCosted]
  | cons y ys ih =>
      simp only [rawListAppendSingletonBitCosted, List.length_cons]
      omega

/-- Instrumented construction of the exact `List.range` result. At successor
`q+1`, the recurrence constructs `range q` and appends `q`. -/
def rawListRangeBitCosted : Nat → List Nat × Nat
  | 0 => ([], 0)
  | q + 1 =>
      let prior := rawListRangeBitCosted q
      let appended := rawListAppendSingletonBitCosted prior.1 q
      (appended.1, prior.2 + appended.2 + 1)

theorem rawListRangeBitCosted_fst (q : Nat) :
    (rawListRangeBitCosted q).1 = List.range q := by
  induction q with
  | zero => simp [rawListRangeBitCosted]
  | succ q ih =>
      simp [rawListRangeBitCosted, ih,
        rawListAppendSingletonBitCosted_fst, List.range_succ]

/-- Constructing the explicit list by the append recurrence costs at most
quadratically many declared list-cell operations. -/
theorem rawListRangeBitCosted_cost_le (q : Nat) :
    (rawListRangeBitCosted q).2 ≤ q * q := by
  induction q with
  | zero => simp [rawListRangeBitCosted]
  | succ q ih =>
      have hpriorLength : (rawListRangeBitCosted q).1.length = q := by
        rw [rawListRangeBitCosted_fst]
        simp
      have happend := rawListAppendSingletonBitCosted_cost_le
        (rawListRangeBitCosted q).1 q
      have hstep : (rawListAppendSingletonBitCosted
          (rawListRangeBitCosted q).1 q).2 ≤ q := by
        simpa [hpriorLength] using happend
      change (rawListRangeBitCosted q).2 +
          (rawListAppendSingletonBitCosted (rawListRangeBitCosted q).1 q).2 + 1 ≤
        (q + 1) * (q + 1)
      nlinarith [ih, hstep]

/-- Each index allocated by the range recurrence fits in at most one more
bit-width unit than the bound on the endpoint. -/
theorem rawListRangeBitCosted_element_width_le (q i : Nat)
    (hi : i ∈ (rawListRangeBitCosted q).1) :
    rawNatBitWidth i ≤ rawNatBitWidth q + 1 := by
  rw [rawListRangeBitCosted_fst] at hi
  have hiq : i < q := by simpa using hi
  have hqbound : q < 2 ^ rawNatBitWidth q := by
    unfold rawNatBitWidth
    exact Nat.lt_log2_self
  have hibound : i < 2 ^ rawNatBitWidth q := lt_trans hiq hqbound
  by_cases hi0 : i = 0
  · simp [rawNatBitWidth, hi0]
  · have hk : 0 < rawNatBitWidth q := by
      unfold rawNatBitWidth
      omega
    have hlog := rawLog2_lt_of_lt_pow hk hibound
    unfold rawNatBitWidth at hlog ⊢
    omega

/-- The constructed range has `q` live cells, each carrying a number whose
binary width is bounded by the endpoint width plus one. -/
theorem rawListRangeBitCosted_space_shape (q : Nat) :
    (rawListRangeBitCosted q).1.length = q ∧
      ∀ i, i ∈ (rawListRangeBitCosted q).1 →
        rawNatBitWidth i ≤ rawNatBitWidth q + 1 := by
  constructor
  · rw [rawListRangeBitCosted_fst]
    simp
  · intro i hi
    exact rawListRangeBitCosted_element_width_le q i hi

end CorruptedFieldRecovery
