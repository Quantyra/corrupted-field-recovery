import CorruptedFieldRecovery.S010BalanceGaussianArrayFlagExecutionTrace

namespace CorruptedFieldRecovery

/-- The counted selector evaluates no more row predicates than there are row
indices. Every evaluated predicate reads one flag; only a fresh row evaluates
the coefficient-array view. The charge counts these designated events; it is
not a complete Lean source-instruction or evaluator-cost count. -/
theorem actualBalanceGaussianFlagCountedFindUnusedRow_trace_bounds
    {m n : Nat} (cells : Array (Array (ZMod 2))) (flags : Array Bool)
    (column : Fin n) (rows : List (Fin m)) :
    let t := (actualBalanceGaussianFlagCountedFindUnusedRow
      cells flags column rows).2
    t.selectorPredicateTests ≤ rows.length ∧
      t.booleanFlagReads = t.selectorPredicateTests ∧
      t.selectorCoefficientViews ≤ t.selectorPredicateTests := by
  induction rows with
  | nil => simp [actualBalanceGaussianFlagCountedFindUnusedRow,
      actualBalanceGaussianFlagExecutionTrace.zero]
  | cons row rows ih =>
      obtain ⟨htests, hreads, hviews⟩ := ih
      cases hflag : actualBalanceGaussianUsedFlagView flags row with
      | true =>
          simp [actualBalanceGaussianFlagCountedFindUnusedRow,
            hflag, actualBalanceGaussianFlagExecutionTrace.add,
            actualBalanceGaussianFlagUsedProbe,
            actualBalanceGaussianFlagExecutionTrace.zero]
          omega
      | false =>
          by_cases hvalue : actualBalanceGaussianArrayView cells row column = 1
          · simp [actualBalanceGaussianFlagCountedFindUnusedRow,
              hflag, hvalue, actualBalanceGaussianFlagFreshProbe,
              actualBalanceGaussianFlagExecutionTrace.zero]
          · simp [actualBalanceGaussianFlagCountedFindUnusedRow,
              hflag, hvalue, actualBalanceGaussianFlagExecutionTrace.add,
              actualBalanceGaussianFlagFreshProbe,
              actualBalanceGaussianFlagExecutionTrace.zero]
            omega

/-- Per-call selector bounds after charging construction of the `Fin` row
list. -/
theorem actualBalanceGaussianFlagCountedFirstUnusedPivotRow_trace_bounds
    {m n : Nat} (cells : Array (Array (ZMod 2))) (flags : Array Bool)
    (column : Fin n) :
    let t := (actualBalanceGaussianFlagCountedFirstUnusedPivotRow
      (m := m) cells flags column).2
    t.rowIndexListNodes = m ∧
      t.selectorPredicateTests ≤ m ∧
      t.booleanFlagReads = t.selectorPredicateTests ∧
      t.selectorCoefficientViews ≤ t.selectorPredicateTests := by
  have h := actualBalanceGaussianFlagCountedFindUnusedRow_trace_bounds
    (m := m) cells flags column (List.ofFn fun row : Fin m => row)
  have hlength : (List.ofFn fun row : Fin m => row).length = m := by
    simp [List.length_ofFn]
  have hzero : ∀ rs : List (Fin m),
      (actualBalanceGaussianFlagCountedFindUnusedRow
        cells flags column rs).2.rowIndexListNodes = 0 := by
    intro rs
    induction rs with
    | nil =>
        simp [actualBalanceGaussianFlagCountedFindUnusedRow,
          actualBalanceGaussianFlagExecutionTrace.zero]
    | cons r rs ih =>
        cases hf : actualBalanceGaussianUsedFlagView flags r with
        | true =>
            simp [actualBalanceGaussianFlagCountedFindUnusedRow, hf,
              actualBalanceGaussianFlagExecutionTrace.add,
              actualBalanceGaussianFlagUsedProbe,
              actualBalanceGaussianFlagExecutionTrace.zero, ih]
        | false =>
            by_cases hv : actualBalanceGaussianArrayView cells r column = 1
            · simp [actualBalanceGaussianFlagCountedFindUnusedRow, hf, hv,
                actualBalanceGaussianFlagFreshProbe,
                actualBalanceGaussianFlagExecutionTrace.zero]
            · simp [actualBalanceGaussianFlagCountedFindUnusedRow, hf, hv,
                actualBalanceGaussianFlagExecutionTrace.add,
                actualBalanceGaussianFlagFreshProbe,
                actualBalanceGaussianFlagExecutionTrace.zero, ih]
  have hz := hzero (List.ofFn fun row : Fin m => row)
  simp only [actualBalanceGaussianFlagCountedFirstUnusedPivotRow,
    actualBalanceGaussianFlagExecutionTrace.add,
    actualBalanceGaussianFlagExecutionTrace.zero, Nat.zero_add]
  rw [hlength] at h
  refine ⟨?_, h.1, h.2.1, h.2.2⟩
  rw [hz]
  exact Nat.add_zero m

/-- The recursive selector trace only ever accumulates selector events: every
other declared component stays zero on any row list. -/
theorem actualBalanceGaussianFlagCountedFindUnusedRow_trace_zero
    {m n : Nat} (cells : Array (Array (ZMod 2))) (flags : Array Bool)
    (column : Fin n) (rows : List (Fin m)) :
    let t := (actualBalanceGaussianFlagCountedFindUnusedRow
      cells flags column rows).2
    t.columnsProcessed = 0 ∧ t.rowIndexListNodes = 0 ∧
      t.pivotUpdates = 0 ∧ t.pivotCoefficientViewsUpper = 0 ∧
      t.pivotRowComparisons = 0 ∧ t.fieldMultiplicationsUpper = 0 ∧
      t.fieldAdditionsUpper = 0 ∧ t.coefficientCellWrites = 0 ∧
      t.matrixRowArrayWrites = 0 ∧ t.flagUpdateReadsUpper = 0 ∧
      t.flagCellComparisons = 0 ∧ t.flagCellWrites = 0 ∧
      t.newMatrixArraySlots = 0 ∧ t.newFlagArraySlots = 0 ∧
      t.initialFlagArraySlots = 0 ∧ t.initialFlagCellWrites = 0 ∧
      t.transcriptCons = 0 ∧ t.columnListNodes = 0 := by
  induction rows with
  | nil =>
      simp [actualBalanceGaussianFlagCountedFindUnusedRow,
        actualBalanceGaussianFlagExecutionTrace.zero]
  | cons row rows ih =>
      cases hflag : actualBalanceGaussianUsedFlagView flags row with
      | true =>
          simp [actualBalanceGaussianFlagCountedFindUnusedRow, hflag,
            actualBalanceGaussianFlagExecutionTrace.add,
            actualBalanceGaussianFlagUsedProbe,
            actualBalanceGaussianFlagExecutionTrace.zero, ih]
      | false =>
          by_cases hvalue : actualBalanceGaussianArrayView cells row column = 1
          · simp [actualBalanceGaussianFlagCountedFindUnusedRow, hflag, hvalue,
              actualBalanceGaussianFlagFreshProbe,
              actualBalanceGaussianFlagExecutionTrace.zero]
          · simp [actualBalanceGaussianFlagCountedFindUnusedRow, hflag, hvalue,
              actualBalanceGaussianFlagExecutionTrace.add,
              actualBalanceGaussianFlagFreshProbe,
              actualBalanceGaussianFlagExecutionTrace.zero, ih]

/-- The counted selector adds only the row-list charge; every other declared
component besides the selector counters is zero. -/
theorem actualBalanceGaussianFlagCountedFirstUnusedPivotRow_trace_zero
    {m n : Nat} (cells : Array (Array (ZMod 2))) (flags : Array Bool)
    (column : Fin n) :
    let t := (actualBalanceGaussianFlagCountedFirstUnusedPivotRow
      (m := m) cells flags column).2
    t.columnsProcessed = 0 ∧ t.pivotUpdates = 0 ∧
      t.pivotCoefficientViewsUpper = 0 ∧ t.pivotRowComparisons = 0 ∧
      t.fieldMultiplicationsUpper = 0 ∧ t.fieldAdditionsUpper = 0 ∧
      t.coefficientCellWrites = 0 ∧ t.matrixRowArrayWrites = 0 ∧
      t.flagUpdateReadsUpper = 0 ∧ t.flagCellComparisons = 0 ∧
      t.flagCellWrites = 0 ∧ t.newMatrixArraySlots = 0 ∧
      t.newFlagArraySlots = 0 ∧ t.initialFlagArraySlots = 0 ∧
      t.initialFlagCellWrites = 0 ∧ t.transcriptCons = 0 ∧
      t.columnListNodes = 0 := by
  have h := actualBalanceGaussianFlagCountedFindUnusedRow_trace_zero
    (m := m) cells flags column (List.ofFn fun row : Fin m => row)
  simp only [actualBalanceGaussianFlagCountedFirstUnusedPivotRow,
    actualBalanceGaussianFlagExecutionTrace.add,
    actualBalanceGaussianFlagExecutionTrace.zero]
  simp [h]

/-- Componentwise trace facts for the complete instrumented flag scan. The
selector work is actual recursive execution; pivot work and allocations are
the conservative per-pivot charges attached by the instrumented scan. -/
theorem actualBalanceGaussianFlagColumnScanInstrumented_trace_components
    {m n : Nat} (cells : Array (Array (ZMod 2))) (flags : Array Bool)
    (columns : List (Fin n)) :
    let run := actualBalanceGaussianFlagColumnScanInstrumented (m := m) cells flags columns
    let t := run.2
    let p := run.1.2.length
    t.columnsProcessed = columns.length ∧
      t.rowIndexListNodes = columns.length * m ∧
      t.selectorPredicateTests ≤ columns.length * m ∧
      t.booleanFlagReads = t.selectorPredicateTests ∧
      t.selectorCoefficientViews ≤ t.selectorPredicateTests ∧
      t.pivotUpdates = p ∧
      t.pivotCoefficientViewsUpper = 3 * p * m * n ∧
      t.pivotRowComparisons = p * m * n ∧
      t.fieldMultiplicationsUpper = p * m * n ∧
      t.fieldAdditionsUpper = p * m * n ∧
      t.coefficientCellWrites = p * m * n ∧
      t.matrixRowArrayWrites = p * m ∧
      t.flagUpdateReadsUpper = p * m ∧
      t.flagCellComparisons = p * m ∧
      t.flagCellWrites = p * m ∧
      t.newMatrixArraySlots = p * m * (n + 1) ∧
      t.newFlagArraySlots = p * m ∧
      t.initialFlagArraySlots = 0 ∧
      t.initialFlagCellWrites = 0 ∧
      t.transcriptCons = p ∧
      t.columnListNodes = 0 := by
  induction columns generalizing cells flags with
  | nil =>
      simp [actualBalanceGaussianFlagColumnScanInstrumented,
        actualBalanceGaussianFlagExecutionTrace.zero]
  | cons column columns ih =>
      let selected := actualBalanceGaussianFlagCountedFirstUnusedPivotRow
        (m := m) cells flags column
      have hselected := actualBalanceGaussianFlagCountedFirstUnusedPivotRow_eq
        (m := m) cells flags column
      have hsearch := actualBalanceGaussianFlagCountedFirstUnusedPivotRow_trace_bounds
        (m := m) cells flags column
      have hzero := actualBalanceGaussianFlagCountedFirstUnusedPivotRow_trace_zero
        (m := m) cells flags column
      have hs_tests :
          (actualBalanceGaussianFlagCountedFirstUnusedPivotRow
            (m := m) cells flags column).2.selectorPredicateTests ≤ m := hsearch.2.1
      have hs_views :
          (actualBalanceGaussianFlagCountedFirstUnusedPivotRow
            (m := m) cells flags column).2.selectorCoefficientViews ≤
          (actualBalanceGaussianFlagCountedFirstUnusedPivotRow
            (m := m) cells flags column).2.selectorPredicateTests := hsearch.2.2.2
      cases hpivot : selected.1 with
      | none =>
          simp only [actualBalanceGaussianFlagColumnScanInstrumented,
            selected, hpivot, actualBalanceGaussianFlagExecutionTrace.add,
            actualBalanceGaussianFlagExecutionTrace.zero]
          have htail := ih cells flags
          have ht_tests := htail.2.2.1
          have ht_views := htail.2.2.2.2.1
          have h_tests :
              (actualBalanceGaussianFlagCountedFirstUnusedPivotRow
                (m := m) cells flags column).2.selectorPredicateTests +
                  (actualBalanceGaussianFlagColumnScanInstrumented (m := m)
                    cells flags columns).2.selectorPredicateTests ≤
                columns.length * m + m := by
            omega
          have h_views :
              (actualBalanceGaussianFlagCountedFirstUnusedPivotRow
                (m := m) cells flags column).2.selectorCoefficientViews +
                  (actualBalanceGaussianFlagColumnScanInstrumented (m := m)
                    cells flags columns).2.selectorCoefficientViews ≤
                (actualBalanceGaussianFlagCountedFirstUnusedPivotRow
                  (m := m) cells flags column).2.selectorPredicateTests +
                  (actualBalanceGaussianFlagColumnScanInstrumented (m := m)
                    cells flags columns).2.selectorPredicateTests := by
            omega
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
            ?_, ?_, ?_, ?_, ?_, ?_⟩
          all_goals
            first
              | simpa only [Nat.zero_add] using h_tests
              | simpa only [Nat.zero_add] using h_views
              | (simp only [hsearch, hzero, htail, List.length_cons,
                  Nat.zero_add, Nat.add_zero]; ring)
              | omega
      | some row =>
          have htail := ih
            (actualBalanceGaussianArrayPivotRow cells row column)
            (actualBalanceGaussianSetUsedFlag flags row)
          have ht_tests := htail.2.2.1
          have ht_views := htail.2.2.2.2.1
          have h_tests :
              (actualBalanceGaussianFlagCountedFirstUnusedPivotRow
                (m := m) cells flags column).2.selectorPredicateTests +
                  (actualBalanceGaussianFlagColumnScanInstrumented (m := m)
                    (actualBalanceGaussianArrayPivotRow cells row column)
                    (actualBalanceGaussianSetUsedFlag flags row)
                    columns).2.selectorPredicateTests ≤
                columns.length * m + m := by
            omega
          have h_views :
              (actualBalanceGaussianFlagCountedFirstUnusedPivotRow
                (m := m) cells flags column).2.selectorCoefficientViews +
                  (actualBalanceGaussianFlagColumnScanInstrumented (m := m)
                    (actualBalanceGaussianArrayPivotRow cells row column)
                    (actualBalanceGaussianSetUsedFlag flags row)
                    columns).2.selectorCoefficientViews ≤
                (actualBalanceGaussianFlagCountedFirstUnusedPivotRow
                  (m := m) cells flags column).2.selectorPredicateTests +
                  (actualBalanceGaussianFlagColumnScanInstrumented (m := m)
                    (actualBalanceGaussianArrayPivotRow cells row column)
                    (actualBalanceGaussianSetUsedFlag flags row)
                    columns).2.selectorPredicateTests := by
            omega
          simp only [actualBalanceGaussianFlagColumnScanInstrumented,
            selected, hpivot, actualBalanceGaussianFlagExecutionTrace.add,
            actualBalanceGaussianFlagPivotUpdateCharge,
            actualBalanceGaussianFlagExecutionTrace.zero]
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
            ?_, ?_, ?_, ?_, ?_, ?_⟩
          all_goals
            first
              | simpa only [Nat.zero_add] using h_tests
              | simpa only [Nat.zero_add] using h_views
              | (simp only [hsearch, hzero, htail, List.length_cons,
                  Nat.zero_add, Nat.add_zero]; ring)
              | omega

/-- The declared primitive charge of the generic instrumented scan is bounded
using the actual pivot count `p`; list cells for the caller-supplied column
list are not included here. -/
theorem actualBalanceGaussianFlagColumnScanInstrumented_sourceUpper
    {m n : Nat} (cells : Array (Array (ZMod 2))) (flags : Array Bool)
    (columns : List (Fin n)) :
    actualBalanceGaussianFlagExecutionTrace.sourceOperationUpper
      (actualBalanceGaussianFlagColumnScanInstrumented (m := m)
        cells flags columns).2 ≤
      5 * columns.length * m +
        10 * (actualBalanceGaussianFlagColumnScanInstrumented (m := m)
          cells flags columns).1.2.length * m * n +
        4 * (actualBalanceGaussianFlagColumnScanInstrumented (m := m)
          cells flags columns).1.2.length * m +
        2 * (actualBalanceGaussianFlagColumnScanInstrumented (m := m)
          cells flags columns).1.2.length + columns.length := by
  let run := actualBalanceGaussianFlagColumnScanInstrumented (m := m) cells flags columns
  let t := run.2
  let p := run.1.2.length
  have hc := actualBalanceGaussianFlagColumnScanInstrumented_trace_components
    (m := m) cells flags columns
  dsimp only [run, t, p] at hc ⊢
  obtain ⟨hcols, hrows, htests, hreads, hviews, hpiv, hviewp, hcomp, hmul,
    hadd, hwrites, houter, hflagreads, hflagcomp, hflagwrites, hmatrixslots,
    hflagslots, hinit, hinitwrite, htranscript, hlist⟩ := hc
  dsimp only [actualBalanceGaussianFlagExecutionTrace.sourceOperationUpper]
  rw [hcols, hrows, hreads, hpiv, hviewp, hcomp, hmul, hadd, hwrites,
    houter, hflagreads, hflagcomp, hflagwrites, hinitwrite, htranscript, hlist]
  omega

/-- A scan has at most one successful pivot per listed column. This is the
executable trace consequence needed to eliminate `p` from the polynomial. -/
theorem actualBalanceGaussianFlagColumnScanInstrumented_pivots_le_columns
    {m n : Nat} (cells : Array (Array (ZMod 2))) (flags : Array Bool)
    (columns : List (Fin n)) :
    (actualBalanceGaussianFlagColumnScanInstrumented (m := m)
      cells flags columns).1.2.length ≤ columns.length := by
  have href := actualBalanceGaussianFlagColumnScanInstrumented_refines
    (m := m) cells flags columns
  have htranscript :
      (actualBalanceGaussianFlagColumnScanInstrumented (m := m) cells flags columns).1.2 =
        (actualBalanceGaussianFlagColumnScan m cells flags columns).2 := by
    simpa using congrArg
      (fun out : ActualBalanceGaussianFlagScanOutput m n => out.2) href
  rw [htranscript]
  exact actualBalanceGaussianFlagColumnScan_pivotCount_le m cells flags columns

/-- Polynomial declared-charge theorem for the raw flag scan. Its trace comes
from the instrumented execution, including the initial false-flag allocation
and construction of the column list. This bounds only the primitive categories
in `ActualBalanceGaussianFlagExecutionTrace.sourceOperationUpper`; it does not
bound Fin-index arithmetic inside `List.ofFn`, loop/branch/call overhead,
implicit array bounds/default machinery beyond the explicitly charged views,
Lean runtime allocation headers, GC, stack space, or bit complexity. -/
theorem actualBalanceGaussianSerializedArrayFlagScanInstrumented_sourceUpper
    {s : Nat} (raw : RawCoefficientArray) (tape : FiveWordTape s) :
    actualBalanceGaussianFlagExecutionTrace.sourceOperationUpper
      (actualBalanceGaussianSerializedArrayFlagScanInstrumented raw tape).2 ≤
      40 * (3 * s) ^ 6 + 36 * (3 * s) ^ 4 + 8 * (3 * s) ^ 2 := by
  let m := 4 * ((3 * s) * (3 * s))
  let k := (3 * s) * (3 * s)
  let cells := actualBalanceSerializedCoefficientMatrix
    (decodeRawArray (n := 3 * s) raw) tape
  let flags := actualBalanceGaussianEmptyUsedFlags m
  let columns := List.ofFn fun column : Fin k => column
  let run := actualBalanceGaussianFlagColumnScanInstrumented (m := m) cells flags columns
  let p := run.1.2.length
  have hp : p ≤ k := by
    dsimp [p, run, columns, k]
    simpa [List.length_ofFn, columns] using
      actualBalanceGaussianFlagColumnScanInstrumented_pivots_le_columns
        (m := m) cells flags columns
  have hscan := actualBalanceGaussianFlagColumnScanInstrumented_sourceUpper
    (m := m) cells flags columns
  have hraw :
      actualBalanceGaussianFlagExecutionTrace.sourceOperationUpper
        (actualBalanceGaussianSerializedArrayFlagScanInstrumented
          raw tape).2 ≤
        5 * k * m + 10 * p * m * k + 4 * p * m + 2 * p + 2 * k + m := by
    have h := hscan
    dsimp only [actualBalanceGaussianSerializedArrayFlagScanInstrumented,
      actualBalanceGaussianFlagExecutionTrace.sourceOperationUpper,
      m, k, cells, flags, columns, run, p] at h ⊢
    simp only [List.length_ofFn] at h ⊢
    omega
  calc
    _ ≤ 5 * k * m + 10 * p * m * k + 4 * p * m + 2 * p + 2 * k + m := hraw
    _ ≤ 5 * k * m + 10 * k * m * k + 4 * k * m + 4 * k + m := by
      have h1 : p * m * k ≤ k * m * k :=
        Nat.mul_le_mul_right k (Nat.mul_le_mul_right m hp)
      have h2 : p * m ≤ k * m := Nat.mul_le_mul_right m hp
      have h3 : 2 * p ≤ 2 * k := Nat.mul_le_mul_left 2 hp
      nlinarith [h1, h2, h3]
    _ = 40 * (3 * s) ^ 6 + 36 * (3 * s) ^ 4 + 8 * (3 * s) ^ 2 := by
      simp [k, m]
      ring

end CorruptedFieldRecovery
