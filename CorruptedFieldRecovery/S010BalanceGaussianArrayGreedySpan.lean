import CorruptedFieldRecovery.S010BalanceGaussianArrayKernelBridge
import CorruptedFieldRecovery.S010BalanceGaussianKernelUniqueness
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.StdBasis

open scoped Matrix
open Module

namespace CorruptedFieldRecovery

/-! # Array-backed greedy span membership

Disjoint proof draft. Given an ordered array of physical columns and a target,
append the target as the final column, run the actual nested-array Gaussian
scan, and inspect its free-variable kernel candidates. A candidate with final
coordinate one is exactly a witness that the target is in the original
column span. This module does not yet prove the quotient-orbit growth or the
three-pass module-basis theorem. -/

/-- The semantic matrix whose columns are the supplied physical vectors,
followed by the target as the last column. -/
def actualGreedyArrayAugmentedMatrix {m : Nat}
    (columns : Array (Fin m → ZMod 2)) (target : Fin m → ZMod 2) :
    Matrix (Fin m) (Fin (columns.size + 1)) (ZMod 2) :=
  fun row col => Fin.lastCases (target row)
    (fun j => columns[j.val]! row) col

/-- Generic row-major serializer local to the greedy-span bridge. -/
def actualGreedyArrayMatrixToArray {m n : Nat}
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) : Array (Array (ZMod 2)) :=
  Array.ofFn fun row : Fin m => Array.ofFn fun col : Fin n => A row col

private theorem actualGreedyArrayMatrixToArray_view {m n : Nat}
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    actualBalanceGaussianArrayView (actualGreedyArrayMatrixToArray A) = A := by
  ext row col
  simp [actualBalanceGaussianArrayView, actualGreedyArrayMatrixToArray]

/-- Row-major serialization of the augmented matrix consumed by the array
scan. -/
def actualGreedyArrayAugmentedCells {m : Nat}
    (columns : Array (Fin m → ZMod 2)) (target : Fin m → ZMod 2) :
    Array (Array (ZMod 2)) :=
  actualGreedyArrayMatrixToArray (actualGreedyArrayAugmentedMatrix columns target)

/-- Reading the row-major augmented array gives the stated finite matrix. -/
theorem actualGreedyArrayAugmentedCells_view {m : Nat}
    (columns : Array (Fin m → ZMod 2)) (target : Fin m → ZMod 2) :
    actualBalanceGaussianArrayView
        (m := m) (n := columns.size + 1)
        (actualGreedyArrayAugmentedCells columns target) =
      actualGreedyArrayAugmentedMatrix columns target := by
  change actualBalanceGaussianArrayView
      (actualGreedyArrayMatrixToArray
        (actualGreedyArrayAugmentedMatrix columns target)) = _
  exact actualGreedyArrayMatrixToArray_view _

/-- The actual full-column array scan of the augmented system. -/
def actualGreedyArrayAugmentedScan {m : Nat}
    (columns : Array (Fin m → ZMod 2)) (target : Fin m → ZMod 2) :=
  actualBalanceGaussianArrayColumnScan
    (m := m) (n := columns.size + 1)
    (actualGreedyArrayAugmentedCells columns target) ∅
    (List.ofFn fun col : Fin (columns.size + 1) => col)

/-- The deterministic matrix scan of the same augmented system has exactly
the matrix view and pivot transcript returned by the actual array scan. -/
theorem actualGreedyArrayAugmentedScan_refines {m : Nat}
    (columns : Array (Fin m → ZMod 2)) (target : Fin m → ZMod 2) :
    (actualBalanceGaussianArrayView
        (m := m) (n := columns.size + 1)
        (actualGreedyArrayAugmentedScan columns target).1,
      (actualGreedyArrayAugmentedScan columns target).2) =
      balanceGaussianColumnScan
        (actualGreedyArrayAugmentedMatrix columns target) ∅
        (List.ofFn fun col : Fin (columns.size + 1) => col) := by
  unfold actualGreedyArrayAugmentedScan
  rw [actualBalanceGaussianArrayColumnScan_refines,
    actualGreedyArrayAugmentedCells_view]

/-- Test whether one scanned column is free and its canonical free-kernel
candidate has coefficient one on the appended target coordinate. -/
def actualGreedyArraySpanCandidateTest {m k : Nat}
    (run : Array (Array (ZMod 2)) × List (Fin m × Fin (k + 1)))
    (column : Fin (k + 1)) : Bool :=
  decide (column ∉ run.2.map Prod.snd) &&
    decide (balanceGaussianFreeKernelCandidate
      (actualBalanceGaussianArrayView (m := m) (n := k + 1) run.1)
      run.2 column (Fin.last k) = 1)

/-- Return the first free-variable witness whose augmented target coordinate
is one. This is a deterministic executable finite scan over column indices. -/
def actualGreedyArraySpanWitness? {m : Nat}
    (columns : Array (Fin m → ZMod 2)) (target : Fin m → ZMod 2) :
    Option (Fin (columns.size + 1)) :=
  let run := actualGreedyArrayAugmentedScan columns target
  (List.ofFn fun col : Fin (columns.size + 1) => col).find?
    (actualGreedyArraySpanCandidateTest run)

private theorem actualGreedyArrayZModTwoCases (x : ZMod 2) :
    x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Matrix view of the supplied physical columns. -/
def actualGreedyArraySpanMatrix {m : Nat}
    (columns : Array (Fin m → ZMod 2)) :
    Matrix (Fin m) (Fin columns.size) (ZMod 2) :=
  fun row col => columns[col.val]! row

/-- The span of an ordered array's columns, represented as the range of its
explicit finite linear-combination map. -/
def actualGreedyArrayColumnSubmodule {m : Nat}
    (columns : Array (Fin m → ZMod 2)) : Submodule (ZMod 2) (Fin m → ZMod 2) :=
  LinearMap.range (Matrix.mulVecLin (actualGreedyArraySpanMatrix columns))

/-- Semantic column-span membership for an array of vectors. -/
def actualGreedyArrayColumnSpanContains {m : Nat}
    (columns : Array (Fin m → ZMod 2)) (target : Fin m → ZMod 2) : Prop :=
  ∃ coeff : Fin columns.size → ZMod 2,
    actualGreedyArraySpanMatrix columns *ᵥ coeff = target

/-- The affine coefficient predicate is exactly membership in the submodule
spanned by the supplied columns. -/
theorem actualGreedyArrayColumnSpanContains_iff_mem_span {m : Nat}
    (columns : Array (Fin m → ZMod 2)) (target : Fin m → ZMod 2) :
    actualGreedyArrayColumnSpanContains columns target ↔
      target ∈ actualGreedyArrayColumnSubmodule columns := by
  rw [actualGreedyArrayColumnSpanContains, actualGreedyArrayColumnSubmodule]
  change (∃ coeff : Fin columns.size → ZMod 2,
      actualGreedyArraySpanMatrix columns *ᵥ coeff = target) ↔
    target ∈ LinearMap.range (Matrix.mulVecLin (actualGreedyArraySpanMatrix columns))
  simp only [LinearMap.mem_range, Matrix.mulVecLin_apply]

/-- Multiplication by the last-column augmentation on `Fin.snoc` coefficients
is the original column combination plus the target. -/
theorem actualGreedyArrayAugmentedMatrix_mulVec_snoc {m : Nat}
    (columns : Array (Fin m → ZMod 2)) (target : Fin m → ZMod 2)
    (coeff : Fin columns.size → ZMod 2) :
    actualGreedyArrayAugmentedMatrix columns target *ᵥ Fin.snoc coeff 1 =
    (actualGreedyArraySpanMatrix columns *ᵥ coeff) + target := by
  funext row
  simp [actualGreedyArrayAugmentedMatrix, actualGreedyArraySpanMatrix,
    Matrix.mulVec, dotProduct,
    Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

/-- Exact equivalence between a semantic column-span witness and a kernel
vector of the augmented matrix whose final coordinate is one. -/
theorem actualGreedyArrayColumnSpan_iff_augmentedKernel {m : Nat}
    (columns : Array (Fin m → ZMod 2)) (target : Fin m → ZMod 2) :
    actualGreedyArrayColumnSpanContains columns target ↔
      ∃ z : Fin (columns.size + 1) → ZMod 2,
        actualGreedyArrayAugmentedMatrix columns target *ᵥ z = 0 ∧
          z (Fin.last columns.size) = 1 := by
  constructor
  · rintro ⟨coeff, hcoeff⟩
    refine ⟨Fin.snoc coeff 1, ?_, ?_⟩
    · rw [actualGreedyArrayAugmentedMatrix_mulVec_snoc, hcoeff]
      apply funext
      intro row
      exact ZModModule.add_self (target row)
    · simp
  · rintro ⟨z, hz, hlast⟩
    let coeff : Fin columns.size → ZMod 2 := fun j => z j.castSucc
    have hzdecomp : z = Fin.snoc coeff 1 := by
      funext i
      refine Fin.lastCases ?_ ?_ i
      · simpa [coeff] using hlast
      · intro j
        simp [coeff, Fin.snoc_castSucc]
    have hsum :
      actualGreedyArraySpanMatrix columns *ᵥ coeff + target = 0 := by
      rw [hzdecomp, actualGreedyArrayAugmentedMatrix_mulVec_snoc] at hz
      exact hz
    refine ⟨coeff, ?_⟩
    apply funext
    intro row
    have hrow := congrFun hsum row
    simp only [Pi.add_apply, Pi.zero_apply] at hrow
    calc
      (actualGreedyArraySpanMatrix columns *ᵥ coeff) row =
          (actualGreedyArraySpanMatrix columns *ᵥ coeff) row + 0 := by simp
      _ = (actualGreedyArraySpanMatrix columns *ᵥ coeff) row +
          (target row + target row) := by
        simp only [ZModModule.add_self, add_zero]
      _ = ((actualGreedyArraySpanMatrix columns *ᵥ coeff) row +
          target row) + target row := by rw [add_assoc]
      _ = 0 + target row := by rw [hrow]
      _ = target row := by simp

private theorem actualGreedyArrayFindTest_of_some {α : Type*}
    (test : α → Bool) (xs : List α) {a : α}
    (h : xs.find? test = some a) : test a = true := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
      by_cases hx : test x = true
      · simp [hx] at h
        subst a
        exact hx
      · simp [hx] at h
        exact ih h

/-- A candidate selected by the array scan is a genuine semantic column-span
witness. -/
theorem actualGreedyArraySpanWitness?_sound {m : Nat}
    (columns : Array (Fin m → ZMod 2)) (target : Fin m → ZMod 2)
    {j : Fin (columns.size + 1)}
    (h : actualGreedyArraySpanWitness? columns target = some j) :
    actualGreedyArrayColumnSpanContains columns target := by
  classical
  let run := actualGreedyArrayAugmentedScan columns target
  have htest : actualGreedyArraySpanCandidateTest run j = true := by
    unfold actualGreedyArraySpanWitness? at h
    exact actualGreedyArrayFindTest_of_some
      (actualGreedyArraySpanCandidateTest run)
      (List.ofFn fun col : Fin (columns.size + 1) => col) h
  have hparts :
      decide (j ∉ run.2.map Prod.snd) = true ∧
      decide (balanceGaussianFreeKernelCandidate
        (actualBalanceGaussianArrayView (m := m) (n := columns.size + 1) run.1)
        run.2 j (Fin.last columns.size) = 1) = true := by
    simpa only [actualGreedyArraySpanCandidateTest, Bool.and_eq_true] using htest
  have hfree : j ∉ run.2.map Prod.snd := of_decide_eq_true hparts.1
  have hlast : balanceGaussianFreeKernelCandidate
      (actualBalanceGaussianArrayView (m := m) (n := columns.size + 1) run.1)
      run.2 j (Fin.last columns.size) = 1 := of_decide_eq_true hparts.2
  have hscan := actualGreedyArrayAugmentedScan_refines columns target
  have hmatrix :
      actualBalanceGaussianArrayView
          (m := m) (n := columns.size + 1)
          (actualGreedyArrayAugmentedScan columns target).1 =
        (balanceGaussianColumnScan
          (actualGreedyArrayAugmentedMatrix columns target) ∅
          (List.ofFn fun col : Fin (columns.size + 1) => col)).1 := by
    simpa only [Prod.fst] using congrArg Prod.fst hscan
  have hpivots :
      (actualGreedyArrayAugmentedScan columns target).2 =
        (balanceGaussianColumnScan
          (actualGreedyArrayAugmentedMatrix columns target) ∅
          (List.ofFn fun col : Fin (columns.size + 1) => col)).2 := by
    simpa only [Prod.snd] using congrArg Prod.snd hscan
  let A := actualGreedyArrayAugmentedMatrix columns target
  let pivots := (balanceGaussianColumnScan A ∅
    (List.ofFn fun col : Fin (columns.size + 1) => col)).2
  have hpivotList : run.2 = pivots := by
    change (actualGreedyArrayAugmentedScan columns target).2 =
      (balanceGaussianColumnScan
        (actualGreedyArrayAugmentedMatrix columns target) ∅
        (List.ofFn fun col : Fin (columns.size + 1) => col)).2
    exact hpivots
  have hrows : (pivots.map Prod.fst).Nodup := by
    simpa [pivots, A] using balanceGaussianColumnScan_pivotRows_nodup
      (List.ofFn fun col : Fin (columns.size + 1) => col) A ∅
  have hunit : ∀ pivot ∈ pivots, ∀ i,
      (balanceGaussianColumnScan A ∅
        (List.ofFn fun col : Fin (columns.size + 1) => col)).1 i pivot.2 =
          if i = pivot.1 then 1 else 0 := by
    intro pivot hpivot i
    exact balanceGaussianColumnScan_recordedPivots_unit
      (List.ofFn fun col : Fin (columns.size + 1) => col) A ∅ pivot hpivot i
  have hzero : ∀ i, i ∉ pivots.map Prod.fst →
      (balanceGaussianColumnScan A ∅
        (List.ofFn fun col : Fin (columns.size + 1) => col)).1 i = 0 := by
    intro i hi
    funext col
    exact balanceGaussianFullColumnScan_unusedRows_zero A i hi col
  have hcandidateKernel :
      (balanceGaussianColumnScan A ∅
        (List.ofFn fun col : Fin (columns.size + 1) => col)).1 *ᵥ
          balanceGaussianFreeKernelCandidate
            (balanceGaussianColumnScan A ∅
              (List.ofFn fun col : Fin (columns.size + 1) => col)).1
            pivots j = 0 := by
    have hfree' : j ∉ pivots.map Prod.snd := by
      rw [← hpivotList]
      exact hfree
    apply balanceGaussianFreeKernelCandidate_mem_ker
      _ pivots j hfree' hrows hunit
    intro i hi
    exact congrFun (hzero i hi) j
  have hkernelArray :
      actualBalanceGaussianArrayView (m := m) (n := columns.size + 1) run.1 *ᵥ
          balanceGaussianFreeKernelCandidate
            (actualBalanceGaussianArrayView (m := m) (n := columns.size + 1) run.1)
            run.2 j = 0 := by
    change actualBalanceGaussianArrayView
        (m := m) (n := columns.size + 1)
        (actualGreedyArrayAugmentedScan columns target).1 *ᵥ
      balanceGaussianFreeKernelCandidate
        (actualBalanceGaussianArrayView
          (m := m) (n := columns.size + 1)
          (actualGreedyArrayAugmentedScan columns target).1)
        (actualGreedyArrayAugmentedScan columns target).2 j = 0
    rw [hmatrix, hpivotList]
    exact hcandidateKernel
  have hkernelInput :=
    (actualBalanceGaussianArrayFullColumnScan_kernel_iff
      (actualGreedyArrayAugmentedCells columns target)
      (balanceGaussianFreeKernelCandidate
        (actualBalanceGaussianArrayView (m := m) (n := columns.size + 1) run.1)
        run.2 j)).mp hkernelArray
  have hinputMatrix :
      actualBalanceGaussianArrayView (m := m) (n := columns.size + 1)
          (actualGreedyArrayAugmentedCells columns target) = A :=
    actualGreedyArrayAugmentedCells_view columns target
  have haug : A *ᵥ
      balanceGaussianFreeKernelCandidate
        (actualBalanceGaussianArrayView (m := m) (n := columns.size + 1) run.1)
        run.2 j = 0 := by
    rw [← hinputMatrix]
    exact hkernelInput
  have hlast' :
      balanceGaussianFreeKernelCandidate
        (actualBalanceGaussianArrayView (m := m) (n := columns.size + 1) run.1)
        run.2 j (Fin.last columns.size) = 1 := by
    simpa using hlast
  exact (actualGreedyArrayColumnSpan_iff_augmentedKernel columns target).mpr
    ⟨balanceGaussianFreeKernelCandidate
        (actualBalanceGaussianArrayView (m := m) (n := columns.size + 1) run.1)
        run.2 j, haug, hlast'⟩

private theorem actualGreedyArrayFindSome_of_exists {α : Type*}
    (test : α → Bool) (xs : List α)
    (hex : ∃ a, a ∈ xs ∧ test a = true) :
    ∃ a, xs.find? test = some a ∧ test a = true := by
  induction xs with
  | nil => simp at hex
  | cons x xs ih =>
      by_cases hx : test x = true
      · exact ⟨x, by simp [hx], hx⟩
      · rcases hex with ⟨a, ha, htest⟩
        rcases List.mem_cons.mp ha with hax | htail
        · subst a
          exact False.elim (hx htest)
        · obtain ⟨b, hb, hbt⟩ := ih ⟨a, htail, htest⟩
          exact ⟨b, by simp [hx, hb], hbt⟩

/-- A consistent augmented system always exposes a free-kernel candidate
with final coordinate one. The reconstruction theorem is essential here: a
single arbitrary kernel candidate is not enough for completeness. -/
theorem actualGreedyArraySpanWitness?_complete {m : Nat}
    (columns : Array (Fin m → ZMod 2)) (target : Fin m → ZMod 2)
    (hspan : actualGreedyArrayColumnSpanContains columns target) :
    ∃ j, actualGreedyArraySpanWitness? columns target = some j := by
  classical
  let run := actualGreedyArrayAugmentedScan columns target
  let A := actualGreedyArrayAugmentedMatrix columns target
  let allColumns := List.ofFn (fun col : Fin (columns.size + 1) => col)
  let scan := balanceGaussianColumnScan A ∅ allColumns
  let pivots := scan.2
  letI : Fintype (balanceGaussianFreeIndex pivots) := Fintype.ofFinite _
  obtain ⟨z, hz, hlast⟩ :=
    (actualGreedyArrayColumnSpan_iff_augmentedKernel columns target).mp hspan
  have hscanPair := actualGreedyArrayAugmentedScan_refines columns target
  have hscanMatrix :
      actualBalanceGaussianArrayView (m := m) (n := columns.size + 1) run.1 = scan.1 := by
    change (actualBalanceGaussianArrayView
        (m := m) (n := columns.size + 1)
        (actualGreedyArrayAugmentedScan columns target).1) =
      (balanceGaussianColumnScan A ∅
        (List.ofFn fun col : Fin (columns.size + 1) => col)).1
    exact congrArg Prod.fst hscanPair
  have hscanPivots : run.2 = pivots := by
    change (actualGreedyArrayAugmentedScan columns target).2 =
      (balanceGaussianColumnScan A ∅
        (List.ofFn fun col : Fin (columns.size + 1) => col)).2
    exact congrArg Prod.snd hscanPair
  have harrayKernel :
      actualBalanceGaussianArrayView (m := m) (n := columns.size + 1) run.1 *ᵥ z = 0 := by
    exact (actualBalanceGaussianArrayFullColumnScan_kernel_iff
      (actualGreedyArrayAugmentedCells columns target) z).mpr (by
        rw [actualGreedyArrayAugmentedCells_view]
        exact hz)
  have hscanKernel : scan.1 *ᵥ z = 0 := by
    rw [← hscanMatrix]
    exact harrayKernel
  have hrepr := balanceGaussianFullColumnScan_candidates_reconstruct A z hscanKernel
  have hexFree :
      ∃ free : balanceGaussianFreeIndex pivots,
        balanceGaussianFreeKernelCandidate scan.1 pivots free.1
          (Fin.last columns.size) = 1 := by
    by_contra hnone
    have hzero : ∀ free : balanceGaussianFreeIndex pivots,
        balanceGaussianFreeKernelCandidate scan.1 pivots free.1
          (Fin.last columns.size) = 0 := by
      intro free
      let value := balanceGaussianFreeKernelCandidate scan.1 pivots free.1
        (Fin.last columns.size)
      have hcases : value = 0 ∨ value = 1 := by
        exact actualGreedyArrayZModTwoCases value
      rcases hcases with h0 | h1
      · exact h0
      · exact False.elim (hnone ⟨free, by simpa [value] using h1⟩)
    have hcoordinate := congrFun hrepr (Fin.last columns.size)
    have hcontradiction : (1 : ZMod 2) = 0 := by
      have hsum : (1 : ZMod 2) =
          ∑ free : balanceGaussianFreeIndex pivots,
            z free.1 * balanceGaussianFreeKernelCandidate
              scan.1 pivots free.1 (Fin.last columns.size) := by
        rw [hlast] at hcoordinate
        simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
          balanceGaussianFreeCandidateFamily] using hcoordinate
      rw [hsum]
      apply Finset.sum_eq_zero
      intro free hfree
      rw [hzero free]
      simp
    exact one_ne_zero hcontradiction
  rcases hexFree with ⟨free, hfreeLast⟩
  have htest : actualGreedyArraySpanCandidateTest run free.1 = true := by
    have hfree : free.1 ∉ run.2.map Prod.snd := by
      simpa only [hscanPivots] using free.property
    have hlast : balanceGaussianFreeKernelCandidate
        (actualBalanceGaussianArrayView run.1) run.2 free.1
        (Fin.last columns.size) = 1 := by
      rw [hscanMatrix, hscanPivots]
      exact hfreeLast
    simp only [actualGreedyArraySpanCandidateTest, Bool.and_eq_true,
      decide_eq_true_eq]
    exact ⟨hfree, hlast⟩
  have hmem : free.1 ∈ allColumns :=
    List.mem_ofFn.mpr ⟨free.1, rfl⟩
  obtain ⟨j, hfind, _⟩ :=
    actualGreedyArrayFindSome_of_exists
      (actualGreedyArraySpanCandidateTest run) allColumns
      ⟨free.1, hmem, htest⟩
  refine ⟨j, ?_⟩
  change (List.ofFn fun col : Fin (columns.size + 1) => col).find?
    (actualGreedyArraySpanCandidateTest
      (actualGreedyArrayAugmentedScan columns target)) = some j
  simpa only [allColumns] using hfind

/-- The executable optional result is complete and sound: it returns a
free-column certificate exactly when the target belongs to the supplied
array's column span. `none` is therefore a proved no-witness result. -/
theorem actualGreedyArraySpanWitness?_isSome_iff {m : Nat}
    (columns : Array (Fin m → ZMod 2)) (target : Fin m → ZMod 2) :
    (actualGreedyArraySpanWitness? columns target).isSome = true ↔
      actualGreedyArrayColumnSpanContains columns target := by
  constructor
  · intro h
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp h
    exact actualGreedyArraySpanWitness?_sound columns target hj
  · intro hspan
    obtain ⟨j, hj⟩ := actualGreedyArraySpanWitness?_complete
      columns target hspan
    exact Option.isSome_iff_exists.mpr ⟨j, hj⟩

/-- The standard physical coordinate vector at index `i`. -/
def actualGreedyArrayUnitVector {n : Nat} (i : Fin n) : Fin n → ZMod 2 :=
  fun j => if j = i then 1 else 0

/-- Boolean predicate used by the deterministic selector. -/
def actualGreedyArrayUnitOutsideTest {n : Nat}
    (columns : Array (Fin n → ZMod 2)) (i : Fin n) : Bool :=
  decide ((actualGreedyArraySpanWitness? columns
    (actualGreedyArrayUnitVector i)).isSome = false)

/-- The actual left-to-right physical-unit scan. It tests only the `n`
standard vectors, using the array-backed span solver above. -/
def actualGreedyArrayFirstUnitOutside? {n : Nat}
    (columns : Array (Fin n → ZMod 2)) : Option (Fin n) :=
  (List.ofFn fun i : Fin n => i).find? (actualGreedyArrayUnitOutsideTest columns)

/-- Every proper current column span has a physical unit outside it. This is
the basis-spanning argument, not a supplied generator assumption. -/
theorem actualGreedyArray_exists_unit_outside
    {n : Nat} (M : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hproper : M ≠ ⊤) :
    ∃ i : Fin n, actualGreedyArrayUnitVector i ∉ M := by
  classical
  have hbasis :
      (fun i : Fin n => actualGreedyArrayUnitVector i) =
        (Pi.basisFun (ZMod 2) (Fin n) : Basis (Fin n) (ZMod 2) (Fin n → ZMod 2)) := by
    funext i
    ext j
    simp [actualGreedyArrayUnitVector, Pi.single_apply]
  have hspan :
      Submodule.span (ZMod 2)
        (Set.range fun i : Fin n => actualGreedyArrayUnitVector i) = ⊤ := by
    rw [hbasis]
    exact (Pi.basisFun (ZMod 2) (Fin n)).span_eq
  by_contra h
  have hforall : ∀ i : Fin n, actualGreedyArrayUnitVector i ∈ M := by
    intro i
    by_contra hi
    exact h ⟨i, hi⟩
  have hle :
      Submodule.span (ZMod 2)
        (Set.range fun i : Fin n => actualGreedyArrayUnitVector i) ≤ M :=
    Submodule.span_le.mpr (Set.range_subset_iff.mpr hforall)
  rw [hspan] at hle
  exact hproper (eq_top_iff.mpr hle)

/-- If the actual selector returns a unit, it is outside the current column
span. -/
theorem actualGreedyArrayFirstUnitOutside?_sound {n : Nat}
    (columns : Array (Fin n → ZMod 2)) {i : Fin n}
    (h : actualGreedyArrayFirstUnitOutside? columns = some i) :
    actualGreedyArrayUnitVector i ∉ actualGreedyArrayColumnSubmodule columns := by
  classical
  have htest :
      actualGreedyArrayUnitOutsideTest columns i = true := by
    change (List.ofFn fun j : Fin n => j).find?
      (actualGreedyArrayUnitOutsideTest columns) = some i at h
    exact actualGreedyArrayFindTest_of_some
      (actualGreedyArrayUnitOutsideTest columns)
      (List.ofFn fun j : Fin n => j) h
  have hnone :
      (actualGreedyArraySpanWitness? columns
        (actualGreedyArrayUnitVector i)).isSome = false := by
    exact of_decide_eq_true htest
  intro hmem
  have hcontains : actualGreedyArrayColumnSpanContains columns
      (actualGreedyArrayUnitVector i) :=
    (actualGreedyArrayColumnSpanContains_iff_mem_span columns _).mpr hmem
  have hsome : (actualGreedyArraySpanWitness? columns
      (actualGreedyArrayUnitVector i)).isSome = true :=
    (actualGreedyArraySpanWitness?_isSome_iff columns _).2 hcontains
  rw [hnone] at hsome
  cases hsome

/-- Whenever the current span is proper, the concrete first-unit selector
returns some outside unit; it cannot stop early. -/
theorem actualGreedyArrayFirstUnitOutside?_some_of_proper {n : Nat}
    (columns : Array (Fin n → ZMod 2))
    (hproper : actualGreedyArrayColumnSubmodule columns ≠ ⊤) :
    ∃ i : Fin n,
      actualGreedyArrayFirstUnitOutside? columns = some i ∧
      actualGreedyArrayUnitVector i ∉ actualGreedyArrayColumnSubmodule columns := by
  classical
  obtain ⟨i, hi⟩ := actualGreedyArray_exists_unit_outside
    (actualGreedyArrayColumnSubmodule columns) hproper
  have hcontainsFalse : ¬ actualGreedyArrayColumnSpanContains columns
      (actualGreedyArrayUnitVector i) := by
    intro hcontains
    exact hi ((actualGreedyArrayColumnSpanContains_iff_mem_span columns _).1 hcontains)
  have hnone : (actualGreedyArraySpanWitness? columns
      (actualGreedyArrayUnitVector i)).isSome = false := by
    cases hresult : (actualGreedyArraySpanWitness? columns
      (actualGreedyArrayUnitVector i)).isSome <;> simp_all [actualGreedyArraySpanWitness?_isSome_iff]
  have htest : actualGreedyArrayUnitOutsideTest columns i = true := by
    simp [actualGreedyArrayUnitOutsideTest, hnone]
  obtain ⟨j, hfind, _⟩ := actualGreedyArrayFindSome_of_exists
    (actualGreedyArrayUnitOutsideTest columns)
    (List.ofFn fun j : Fin n => j)
    ⟨i, List.mem_ofFn.mpr ⟨i, rfl⟩, htest⟩
  refine ⟨j, hfind, ?_⟩
  exact actualGreedyArrayFirstUnitOutside?_sound columns hfind

/-- If the selector returns `none`, every physical unit is in the span, so
the span is the whole space. This is the explicit no-witness meaning of the
actual scan result. -/
theorem actualGreedyArrayFirstUnitOutside?_none_implies_top {n : Nat}
    (columns : Array (Fin n → ZMod 2))
    (hnone : actualGreedyArrayFirstUnitOutside? columns = none) :
    actualGreedyArrayColumnSubmodule columns = ⊤ := by
  classical
  have hspanUnits :
      Submodule.span (ZMod 2)
        (Set.range fun i : Fin n => actualGreedyArrayUnitVector i) = ⊤ := by
    rw [show (fun i : Fin n => actualGreedyArrayUnitVector i) =
      (Pi.basisFun (ZMod 2) (Fin n) : Basis (Fin n) (ZMod 2) (Fin n → ZMod 2)) by
        funext i
        ext j
        simp [actualGreedyArrayUnitVector, Pi.single_apply]]
    exact (Pi.basisFun (ZMod 2) (Fin n)).span_eq
  have hunit : ∀ i : Fin n,
      actualGreedyArrayUnitVector i ∈ actualGreedyArrayColumnSubmodule columns := by
    intro i
    have hnotTest :
        actualGreedyArrayUnitOutsideTest columns i ≠ true := by
      intro ht
      change (List.ofFn fun j : Fin n => j).find?
        (actualGreedyArrayUnitOutsideTest columns) = none at hnone
      obtain ⟨j, hfind, _⟩ := actualGreedyArrayFindSome_of_exists
        (actualGreedyArrayUnitOutsideTest columns)
        (List.ofFn fun j : Fin n => j)
        ⟨i, List.mem_ofFn.mpr ⟨i, rfl⟩, ht⟩
      rw [hnone] at hfind
      cases hfind
    have hsome : (actualGreedyArraySpanWitness? columns
        (actualGreedyArrayUnitVector i)).isSome = true := by
      cases hresult : (actualGreedyArraySpanWitness? columns
          (actualGreedyArrayUnitVector i)).isSome with
      | false => exact False.elim (hnotTest (by simp [actualGreedyArrayUnitOutsideTest, hresult]))
      | true => rfl
    exact (actualGreedyArrayColumnSpanContains_iff_mem_span columns _).1
      ((actualGreedyArraySpanWitness?_isSome_iff columns _).1 hsome)
  have hle : actualGreedyArrayColumnSubmodule columns = ⊤ := by
    apply eq_top_iff.mpr
    rw [← hspanUnits]
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact hunit i
  exact hle

end CorruptedFieldRecovery
