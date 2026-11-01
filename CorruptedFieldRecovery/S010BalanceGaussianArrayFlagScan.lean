import CorruptedFieldRecovery.S010BalanceGaussianArrayDeterministicScan

open scoped Matrix

namespace CorruptedFieldRecovery

/-- Read one used-row bit. Missing positions default to `false`; the
algorithm's initializer and update preserve an array of exactly `m` bits. -/
def actualBalanceGaussianUsedFlagView {m : Nat}
    (flags : Array Bool) (row : Fin m) : Bool :=
  (flags[row.val]?.getD false)

/-- Set one used-row bit by rebuilding a fixed-length Boolean array. This
avoids the opaque `Finset` membership and insertion operations in the
computational path, at the cost of `m` bit tests/writes per successful pivot. -/
def actualBalanceGaussianSetUsedFlag {m : Nat}
    (flags : Array Bool) (row : Fin m) : Array Bool :=
  Array.ofFn fun i : Fin m =>
    if i = row then true else actualBalanceGaussianUsedFlagView flags i

theorem actualBalanceGaussianSetUsedFlag_view {m : Nat}
    (flags : Array Bool) (row i : Fin m) :
    actualBalanceGaussianUsedFlagView
      (actualBalanceGaussianSetUsedFlag flags row) i =
        if i = row then true else actualBalanceGaussianUsedFlagView flags i := by
  simp [actualBalanceGaussianSetUsedFlag, actualBalanceGaussianUsedFlagView]

/-- Deterministic first-unused-pivot search using a Boolean flag array and
the nested coefficient-array view. The row order is the standard `Fin` order.
The row count `m` is explicit because it is not determined by the flag or cell
arrays alone. -/
def actualBalanceGaussianFlagFirstUnusedPivotRow (m : Nat) {n : Nat}
    (cells : Array (Array (ZMod 2))) (flags : Array Bool)
    (column : Fin n) : Option (Fin m) :=
  (List.ofFn fun row : Fin m => row).find? fun row =>
    decide ((if actualBalanceGaussianUsedFlagView flags row then
      (0 : ZMod 2) else actualBalanceGaussianArrayView cells row column) = 1)

/-- If the flag array represents a used-row set, its pivot search is exactly
the accepted deterministic matrix selector. -/
theorem actualBalanceGaussianFlagFirstUnusedPivotRow_eq
    {m n : Nat} (cells : Array (Array (ZMod 2))) (flags : Array Bool)
    (column : Fin n) (used : Finset (Fin m))
    (hflags : ∀ row, actualBalanceGaussianUsedFlagView flags row =
      decide (row ∈ used)) :
    actualBalanceGaussianFlagFirstUnusedPivotRow m cells flags column =
      balanceFirstUnusedPivotRow (actualBalanceGaussianArrayView cells)
        column used := by
  unfold actualBalanceGaussianFlagFirstUnusedPivotRow
    balanceFirstUnusedPivotRow balanceFirstPivotRow balanceMaskUsedRows
  congr 1
  funext row
  rw [hflags row]
  by_cases hu : row ∈ used <;> simp [hu]

/-- Initialize all used-row flags to false. -/
def actualBalanceGaussianEmptyUsedFlags (m : Nat) : Array Bool :=
  Array.ofFn fun _ : Fin m => false

theorem actualBalanceGaussianEmptyUsedFlags_correct {m : Nat} :
    ∀ row : Fin m,
      actualBalanceGaussianUsedFlagView
        (actualBalanceGaussianEmptyUsedFlags m) row = decide (row ∈ (∅ : Finset (Fin m))) := by
  intro row
  simp [actualBalanceGaussianEmptyUsedFlags,
    actualBalanceGaussianUsedFlagView]

/-- Updating flags preserves the correspondence with `insert`, given that the
new pivot row was fresh. -/
theorem actualBalanceGaussianSetUsedFlag_correct {m : Nat}
    (flags : Array Bool) (row : Fin m) (used : Finset (Fin m))
    (hflags : ∀ i, actualBalanceGaussianUsedFlagView flags i = decide (i ∈ used))
    (hfresh : row ∉ used) :
    ∀ i, actualBalanceGaussianUsedFlagView
      (actualBalanceGaussianSetUsedFlag flags row) i =
        decide (i ∈ insert row used) := by
  intro i
  rw [actualBalanceGaussianSetUsedFlag_view]
  by_cases hi : i = row
  · subst i
    simp [hfresh]
  · simp [hi, hflags i]

/-- Run the deterministic column scan using only an array of used-row flags
for selection state. The returned transcript records exactly the row updates
performed on the nested coefficient array. -/
def actualBalanceGaussianFlagColumnScan (m : Nat) {n : Nat}
    (cells : Array (Array (ZMod 2))) :
    Array Bool → List (Fin n) →
      (Array (Array (ZMod 2)) × Array Bool) × List (Fin m × Fin n)
  | flags, [] => ((cells, flags), [])
  | flags, column :: columns =>
      match actualBalanceGaussianFlagFirstUnusedPivotRow m cells flags column with
      | none => actualBalanceGaussianFlagColumnScan m cells flags columns
      | some row =>
          let rest := actualBalanceGaussianFlagColumnScan m
            (actualBalanceGaussianArrayPivotRow cells row column)
            (actualBalanceGaussianSetUsedFlag flags row) columns
          ((rest.1.1, rest.1.2), (row, column) :: rest.2)

/-- The flag-array implementation refines the accepted matrix scan whenever
its flags represent the matrix scan's `used` set. -/
theorem actualBalanceGaussianFlagColumnScan_refines
    {m n : Nat} (cells : Array (Array (ZMod 2))) (flags : Array Bool)
    (used : Finset (Fin m)) (columns : List (Fin n))
    (hflags : ∀ row, actualBalanceGaussianUsedFlagView flags row =
      decide (row ∈ used)) :
    (actualBalanceGaussianArrayView
        (actualBalanceGaussianFlagColumnScan m cells flags columns).1.1,
      (actualBalanceGaussianFlagColumnScan m cells flags columns).2) =
      balanceGaussianColumnScan (actualBalanceGaussianArrayView cells)
        used columns := by
  induction columns generalizing cells flags used with
  | nil => rfl
  | cons column columns ih =>
      have hsearch := actualBalanceGaussianFlagFirstUnusedPivotRow_eq
        cells flags column used hflags
      simp only [actualBalanceGaussianFlagColumnScan]
      cases h : actualBalanceGaussianFlagFirstUnusedPivotRow m cells flags column with
      | none =>
          have hpivot : balanceFirstUnusedPivotRow
              (actualBalanceGaussianArrayView cells) column used = none := by
            rw [← hsearch]
            exact h
          simp only [balanceGaussianColumnScan, hpivot]
          exact ih cells flags used hflags
      | some row =>
          have hpivot : balanceFirstUnusedPivotRow
              (actualBalanceGaussianArrayView cells) column used = some row := by
            rw [← hsearch]
            exact h
          have hfresh : row ∉ used :=
            (balanceFirstUnusedPivotRow_sound
              (actualBalanceGaussianArrayView cells) column used hpivot).1
          have hflags' := actualBalanceGaussianSetUsedFlag_correct
            flags row used hflags hfresh
          simp only [balanceGaussianColumnScan, hpivot]
          have hres := ih (actualBalanceGaussianArrayPivotRow cells row column)
            (actualBalanceGaussianSetUsedFlag flags row) (insert row used) hflags'
          rw [actualBalanceGaussianArrayPivotRow_view_eq] at hres
          simpa using Prod.ext_iff.mp hres

/-- Serialized raw balance scan using Boolean flags. No `Finset` is used in
the executable selector/update loop; the initial flags are all false. -/
def actualBalanceGaussianSerializedArrayFlagScan {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s) :=
  actualBalanceGaussianFlagColumnScan (4 * ((3 * s) * (3 * s)))
    (actualBalanceSerializedCoefficientMatrix
      (decodeRawArray (n := 3 * s) raw) tape)
    (actualBalanceGaussianEmptyUsedFlags (4 * ((3 * s) * (3 * s))))
    (List.ofFn fun column : Fin ((3 * s) * (3 * s)) => column)

theorem actualBalanceGaussianSerializedArrayFlagScan_refines
    {s : Nat} (raw : RawCoefficientArray) (tape : FiveWordTape s) :
    (actualBalanceGaussianArrayView
        (actualBalanceGaussianSerializedArrayFlagScan raw tape).1.1,
      (actualBalanceGaussianSerializedArrayFlagScan raw tape).2) =
      actualBalanceGaussianRawScan raw tape := by
  have hrefine := actualBalanceGaussianFlagColumnScan_refines
    (m := 4 * ((3 * s) * (3 * s)))
    (cells := actualBalanceSerializedCoefficientMatrix
      (decodeRawArray (n := 3 * s) raw) tape)
    (flags := actualBalanceGaussianEmptyUsedFlags (4 * ((3 * s) * (3 * s))))
    (used := (∅ : Finset (Fin (4 * ((3 * s) * (3 * s))))))
    (columns := List.ofFn fun column : Fin ((3 * s) * (3 * s)) => column)
    (actualBalanceGaussianEmptyUsedFlags_correct
      (m := 4 * ((3 * s) * (3 * s))))
  simpa [actualBalanceGaussianSerializedArrayFlagScan,
    actualBalanceGaussianRawScan,
    actualBalanceGaussianSerializedArrayView_eq_rawMatrix] using hrefine

/-- Source-level unit-cost model for the flag-array scan. The model explicitly
charges row-list construction/traversal, one Boolean flag read per tested row,
coefficient array views, per-cell pivot work, flag-array rebuilding, and the
pivot transcript. It does not model compiled Lean runtime behavior. -/
structure ActualBalanceGaussianFlagScanCost where
  rowListNodes : Nat
  rowPredicateTests : Nat
  booleanFlagReads : Nat
  selectorCoefficientViewsUpper : Nat
  pivotCoefficientViewsUpper : Nat
  rowComparisons : Nat
  fieldMultiplicationsUpper : Nat
  fieldAdditionsUpper : Nat
  matrixCellWrites : Nat
  matrixRowArrayWrites : Nat
  flagUpdateReadsUpper : Nat
  flagCellComparisons : Nat
  flagCellWrites : Nat
  newMatrixArraySlots : Nat
  newFlagArraySlots : Nat
  initialFlagArraySlots : Nat
  initialFlagCellWrites : Nat
  liveMatrixArraySlotsUpper : Nat
  liveFlagArraySlotsUpper : Nat
  liveArrayAndListSlotsUpper : Nat
  transcriptNodes : Nat
  pivotBranchSteps : Nat
  columnScanSteps : Nat
  columnListNodes : Nat
  deriving DecidableEq, Repr

def actualBalanceGaussianFlagScanCostModel (m n k p : Nat) :
    ActualBalanceGaussianFlagScanCost :=
  { rowListNodes := k * m
    rowPredicateTests := k * m
    booleanFlagReads := k * m
    selectorCoefficientViewsUpper := k * m
    pivotCoefficientViewsUpper := 3 * p * m * n
    rowComparisons := p * m * n
    fieldMultiplicationsUpper := p * m * n
    fieldAdditionsUpper := p * m * n
    matrixCellWrites := p * m * n
    matrixRowArrayWrites := p * m
    flagUpdateReadsUpper := p * m
    flagCellComparisons := p * m
    flagCellWrites := p * m
    newMatrixArraySlots := p * m * (n + 1)
    newFlagArraySlots := p * m
    initialFlagArraySlots := 0
    initialFlagCellWrites := 0
    liveMatrixArraySlotsUpper := (p + 2) * m * (n + 1)
    liveFlagArraySlotsUpper := (p + 2) * m
    liveArrayAndListSlotsUpper :=
      (p + 2) * m * (n + 2) + m + p + k
    transcriptNodes := p
    pivotBranchSteps := p
    columnScanSteps := k
    columnListNodes := k }

def ActualBalanceGaussianFlagScanCost.sourceOperations
    (cost : ActualBalanceGaussianFlagScanCost) : Nat :=
  cost.rowListNodes + cost.rowPredicateTests + cost.booleanFlagReads +
    2 * cost.selectorCoefficientViewsUpper +
    2 * cost.pivotCoefficientViewsUpper + cost.rowComparisons +
    cost.fieldMultiplicationsUpper + cost.fieldAdditionsUpper +
    cost.matrixCellWrites + cost.matrixRowArrayWrites +
    cost.flagUpdateReadsUpper + cost.flagCellComparisons + cost.flagCellWrites +
    cost.initialFlagCellWrites + cost.transcriptNodes +
    cost.pivotBranchSteps + cost.columnScanSteps + cost.columnListNodes

theorem actualBalanceGaussianFlagScanCostModel_sourceOperations_eq
    (m n k p : Nat) :
    (actualBalanceGaussianFlagScanCostModel m n k p).sourceOperations =
      5 * k * m + 10 * p * m * n + 4 * p * m + 2 * p + 2 * k := by
  simp [actualBalanceGaussianFlagScanCostModel,
    ActualBalanceGaussianFlagScanCost.sourceOperations]
  ring

theorem actualBalanceGaussianFlagScanCostModel_sourceOperations_le
    (m n k p : Nat) (hp : p ≤ k) :
    (actualBalanceGaussianFlagScanCostModel m n k p).sourceOperations ≤
      9 * k * m + 10 * k * m * n + 4 * k := by
  rw [actualBalanceGaussianFlagScanCostModel_sourceOperations_eq]
  have h1 : p * m * n ≤ k * m * n :=
    Nat.mul_le_mul_right n (Nat.mul_le_mul_right m hp)
  have h2 : p * m ≤ k * m := Nat.mul_le_mul_right m hp
  have h3 : 2 * p ≤ 2 * k := Nat.mul_le_mul_left 2 hp
  nlinarith [h1, h2, h3]

/-- Cumulative array slots are the update output sizes; the live bound keeps
all previous array versions plus one in-progress output conservatively. -/
theorem actualBalanceGaussianFlagScanCostModel_space_bounds
    (m n k p : Nat) (hp : p ≤ k) :
    (actualBalanceGaussianFlagScanCostModel m n k p).newMatrixArraySlots +
        (actualBalanceGaussianFlagScanCostModel m n k p).newFlagArraySlots ≤
      k * m * (n + 2) ∧
    (actualBalanceGaussianFlagScanCostModel m n k p).liveArrayAndListSlotsUpper ≤
      (k + 2) * m * (n + 2) + m + 2 * k := by
  constructor
  · show p * m * (n + 1) + p * m ≤ k * m * (n + 2)
    have hstep : p * m * (n + 1) + p * m = p * m * (n + 2) := by ring
    rw [hstep]
    exact Nat.mul_le_mul_right (n + 2) (Nat.mul_le_mul_right m hp)
  · show (p + 2) * m * (n + 2) + m + p + k ≤
      (k + 2) * m * (n + 2) + m + 2 * k
    have h1 : (p + 2) * m * (n + 2) ≤ (k + 2) * m * (n + 2) :=
      Nat.mul_le_mul_right (n + 2)
        (Nat.mul_le_mul_right m (Nat.add_le_add_right hp 2))
    nlinarith [h1]

/-- The scan performs at most one pivot update per input column. -/
theorem actualBalanceGaussianFlagColumnScan_pivotCount_le
    (m : Nat) {n : Nat} (cells : Array (Array (ZMod 2))) (flags : Array Bool)
    (columns : List (Fin n)) :
    (actualBalanceGaussianFlagColumnScan m cells flags columns).2.length ≤
      columns.length := by
  induction columns generalizing cells flags with
  | nil => simp [actualBalanceGaussianFlagColumnScan]
  | cons column columns ih =>
      simp only [actualBalanceGaussianFlagColumnScan]
      cases h : actualBalanceGaussianFlagFirstUnusedPivotRow m cells flags column with
      | none =>
          simpa using
            Nat.le_trans (ih cells flags) (Nat.le_succ columns.length)
      | some row =>
          simpa using
            Nat.succ_le_succ
              (ih (actualBalanceGaussianArrayPivotRow cells row column)
                (actualBalanceGaussianSetUsedFlag flags row))

/-- For a scan with `k` columns, its source-level operation model uses the
actual pivot count from the returned transcript. -/
def actualBalanceGaussianFlagColumnScanCost (m : Nat) {n : Nat}
    (cells : Array (Array (ZMod 2))) (flags : Array Bool)
    (columns : List (Fin n)) : ActualBalanceGaussianFlagScanCost :=
  actualBalanceGaussianFlagScanCostModel m n columns.length
    (actualBalanceGaussianFlagColumnScan m cells flags columns).2.length

theorem actualBalanceGaussianFlagColumnScanCost_sourceOperations_le
    (m : Nat) {n : Nat} (cells : Array (Array (ZMod 2))) (flags : Array Bool)
    (columns : List (Fin n)) :
    (actualBalanceGaussianFlagColumnScanCost m cells flags columns).sourceOperations ≤
      9 * columns.length * m + 10 * columns.length * m * n +
        4 * columns.length := by
  exact actualBalanceGaussianFlagScanCostModel_sourceOperations_le m n
    columns.length _
    (actualBalanceGaussianFlagColumnScan_pivotCount_le m cells flags columns)

/-- Overwriting the initial-flag fields adds exactly the initial-flag cell
charges to the source-operation sum, provided the base cost has no initial-flag
writes. -/
theorem ActualBalanceGaussianFlagScanCost.sourceOperations_updateInit
    (cost : ActualBalanceGaussianFlagScanCost) (t : Nat)
    (hzero : cost.initialFlagCellWrites = 0) :
    ({ cost with initialFlagArraySlots := t, initialFlagCellWrites := t } :
        ActualBalanceGaussianFlagScanCost).sourceOperations =
      cost.sourceOperations + t := by
  simp only [ActualBalanceGaussianFlagScanCost.sourceOperations]
  rw [hzero]
  ring

/-- Overwriting the initial-flag fields replaces the initial array-slot term. -/
theorem ActualBalanceGaussianFlagScanCost.newSlots_updateInit
    (cost : ActualBalanceGaussianFlagScanCost) (t : Nat) :
    ({ cost with initialFlagArraySlots := t, initialFlagCellWrites := t } :
        ActualBalanceGaussianFlagScanCost).newMatrixArraySlots +
      ({ cost with initialFlagArraySlots := t, initialFlagCellWrites := t } :
        ActualBalanceGaussianFlagScanCost).newFlagArraySlots +
      ({ cost with initialFlagArraySlots := t, initialFlagCellWrites := t } :
        ActualBalanceGaussianFlagScanCost).initialFlagArraySlots =
      cost.newMatrixArraySlots + cost.newFlagArraySlots + t := by
  simp

/-- Cost of the raw wrapper includes construction of its initial all-false flag
array. The generic scan cost above assumes the caller supplies the flags. -/
def actualBalanceGaussianSerializedArrayFlagScanCost {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s) :
    ActualBalanceGaussianFlagScanCost :=
  { actualBalanceGaussianFlagColumnScanCost (4 * ((3 * s) * (3 * s)))
      (actualBalanceSerializedCoefficientMatrix
        (decodeRawArray (n := 3 * s) raw) tape)
      (actualBalanceGaussianEmptyUsedFlags (4 * ((3 * s) * (3 * s))))
      (List.ofFn fun column : Fin ((3 * s) * (3 * s)) => column) with
    initialFlagArraySlots := 4 * ((3 * s) * (3 * s))
    initialFlagCellWrites := 4 * ((3 * s) * (3 * s)) }

/-- The raw balanced system has `m=4*d^2`, `n=k=d^2`, `d=3*s`, so the
source-level flag-array model including flag initialization charges at most
`40*d^6 + 36*d^4 + 8*d^2`
operations. Array accesses are unit-cost primitives only in this declared
model; no compiler/runtime bit bound is claimed. -/
theorem actualBalanceGaussianSerializedArrayFlagScan_sourceOperations_le
    {s : Nat} (raw : RawCoefficientArray) (tape : FiveWordTape s) :
    (actualBalanceGaussianSerializedArrayFlagScanCost raw tape).sourceOperations ≤
        40 * (3 * s) ^ 6 + 36 * (3 * s) ^ 4 + 8 * (3 * s) ^ 2 := by
  let d := (3 * s) * (3 * s)
  let m := 4 * d
  let cells := actualBalanceSerializedCoefficientMatrix
    (decodeRawArray (n := 3 * s) raw) tape
  let flags := actualBalanceGaussianEmptyUsedFlags m
  let columns : List (Fin d) := List.ofFn fun column : Fin d => column
  have hbase := actualBalanceGaussianFlagColumnScanCost_sourceOperations_le
    m cells flags columns
  have hval :
      (actualBalanceGaussianSerializedArrayFlagScanCost raw tape).sourceOperations =
        (actualBalanceGaussianFlagColumnScanCost m cells flags columns).sourceOperations + m := by
    have hzero :
        (actualBalanceGaussianFlagColumnScanCost m cells flags columns).initialFlagCellWrites = 0 := rfl
    unfold actualBalanceGaussianSerializedArrayFlagScanCost
    rw [ActualBalanceGaussianFlagScanCost.sourceOperations_updateInit _ m hzero]
  rw [hval]
  calc
    _ ≤ (9 * columns.length * m + 10 * columns.length * m * d +
          4 * columns.length) + m := Nat.add_le_add_right hbase m
    _ = 40 * (3 * s) ^ 6 + 36 * (3 * s) ^ 4 + 8 * (3 * s) ^ 2 := by
        simp [columns, d, m, List.length_ofFn]
        ring

/-- Raw-system cumulative and peak array/list slots in the declared model.
This omits source tensor construction, call frames, object headers, and GC. -/
theorem actualBalanceGaussianSerializedArrayFlagScan_space_le_polynomial
    {s : Nat} (raw : RawCoefficientArray) (tape : FiveWordTape s) :
    let cost := actualBalanceGaussianSerializedArrayFlagScanCost raw tape
    cost.newMatrixArraySlots + cost.newFlagArraySlots +
        cost.initialFlagArraySlots ≤
        4 * (3 * s) ^ 6 + 8 * (3 * s) ^ 4 + 4 * (3 * s) ^ 2 ∧
      cost.liveArrayAndListSlotsUpper ≤
        4 * (3 * s) ^ 6 + 16 * (3 * s) ^ 4 + 22 * (3 * s) ^ 2 := by
  let d := (3 * s) * (3 * s)
  let m := 4 * d
  let cells := actualBalanceSerializedCoefficientMatrix
    (decodeRawArray (n := 3 * s) raw) tape
  let flags := actualBalanceGaussianEmptyUsedFlags m
  let columns : List (Fin d) := List.ofFn fun column : Fin d => column
  have hp : (actualBalanceGaussianFlagColumnScan m cells flags columns).2.length ≤
      columns.length :=
    actualBalanceGaussianFlagColumnScan_pivotCount_le m cells flags columns
  have hspace := actualBalanceGaussianFlagScanCostModel_space_bounds m d columns.length
    (actualBalanceGaussianFlagColumnScan m cells flags columns).2.length hp
  have hval :
      (actualBalanceGaussianSerializedArrayFlagScanCost raw tape).newMatrixArraySlots +
          (actualBalanceGaussianSerializedArrayFlagScanCost raw tape).newFlagArraySlots +
          (actualBalanceGaussianSerializedArrayFlagScanCost raw tape).initialFlagArraySlots =
        (actualBalanceGaussianFlagColumnScanCost m cells flags columns).newMatrixArraySlots +
          (actualBalanceGaussianFlagColumnScanCost m cells flags columns).newFlagArraySlots + m := by
    unfold actualBalanceGaussianSerializedArrayFlagScanCost
    rw [ActualBalanceGaussianFlagScanCost.newSlots_updateInit]
  have hlive :
      (actualBalanceGaussianSerializedArrayFlagScanCost raw tape).liveArrayAndListSlotsUpper =
        (actualBalanceGaussianFlagColumnScanCost m cells flags columns).liveArrayAndListSlotsUpper := by
    unfold actualBalanceGaussianSerializedArrayFlagScanCost
    rfl
  dsimp only
  constructor
  · rw [hval]
    calc
      _ ≤ columns.length * m * (d + 2) + m := Nat.add_le_add_right hspace.1 m
      _ = 4 * (3 * s) ^ 6 + 8 * (3 * s) ^ 4 + 4 * (3 * s) ^ 2 := by
          simp [columns, d, m, List.length_ofFn]
          ring
  · rw [hlive]
    calc
      _ ≤ (columns.length + 2) * m * (d + 2) + m + 2 * columns.length :=
        hspace.2
      _ = 4 * (3 * s) ^ 6 + 16 * (3 * s) ^ 4 + 22 * (3 * s) ^ 2 := by
          simp [columns, d, m, List.length_ofFn]
          ring

end CorruptedFieldRecovery
