import CorruptedFieldRecovery.S010QInputEquivalence
import CorruptedFieldRecovery.S010GoodTapeBilinearBalance
import CorruptedFieldRecovery.FourContractions

namespace CorruptedFieldRecovery

noncomputable section

private theorem fieldDet3_add_first {K : Type*} [CommRing K]
    (x x' y z : FieldTriple K) :
    fieldDet3 (x + x') y z = fieldDet3 x y z + fieldDet3 x' y z := by
  rcases x with ⟨x₀, x₁, x₂⟩
  rcases x' with ⟨x₀', x₁', x₂'⟩
  simp [fieldDet3]
  ring

private theorem fieldDet3_add_second {K : Type*} [CommRing K]
    (x y y' z : FieldTriple K) :
    fieldDet3 x (y + y') z = fieldDet3 x y z + fieldDet3 x y' z := by
  rcases y with ⟨y₀, y₁, y₂⟩
  rcases y' with ⟨y₀', y₁', y₂'⟩
  simp [fieldDet3]
  ring

private theorem fieldDet3_add_third {K : Type*} [CommRing K]
    (x y z z' : FieldTriple K) :
    fieldDet3 x y (z + z') = fieldDet3 x y z + fieldDet3 x y z' := by
  rcases z with ⟨z₀, z₁, z₂⟩
  rcases z' with ⟨z₀', z₁', z₂'⟩
  simp [fieldDet3]
  ring

private theorem fieldDet3_smul_third {K : Type*} [CommRing K]
    (a : K) (x y z : FieldTriple K) :
    fieldDet3 x y (a • z) = a * fieldDet3 x y z := by
  rcases z with ⟨z₀, z₁, z₂⟩
  simp [fieldDet3, smul_eq_mul]
  ring

private theorem fieldDet3_binary_smul_first
    {K : Type*} [CommRing K] [Algebra BinaryField K]
    (a : BinaryField) (x y z : FieldTriple K) :
    fieldDet3 (a • x) y z = algebraMap BinaryField K a * fieldDet3 x y z := by
  rw [show a • x = (algebraMap BinaryField K a) • x by
    simp [Algebra.smul_def]]
  rw [fieldDet3_smul_left]

private theorem fieldDet3_binary_smul_second
    {K : Type*} [CommRing K] [Algebra BinaryField K]
    (a : BinaryField) (x y z : FieldTriple K) :
    fieldDet3 x (a • y) z = algebraMap BinaryField K a * fieldDet3 x y z := by
  rw [show a • y = (algebraMap BinaryField K a) • y by
    simp [Algebra.smul_def]]
  rw [fieldDet3_smul_right]

private theorem fieldDet3_binary_smul_third
    {K : Type*} [CommRing K] [Algebra BinaryField K]
    (a : BinaryField) (x y z : FieldTriple K) :
    fieldDet3 x y (a • z) = algebraMap BinaryField K a * fieldDet3 x y z := by
  rw [show a • z = (algebraMap BinaryField K a) • z by
    simp [Algebra.smul_def]]
  rw [fieldDet3_smul_third]

set_option maxHeartbeats 2000000 in
private def qTraceDeterminantThird
    {K : Type*} [Field K] [Finite K] [Algebra BinaryField K]
    {n : Nat} (Q : BinaryVector n ≃ₗ[BinaryField] FieldTriple K) (c : K)
    (x y : BinaryVector n) : BinaryVector n →ₗ[BinaryField] BinaryField where
  toFun z := Algebra.trace BinaryField K (c * fieldDet3 (Q x) (Q y) (Q z))
  map_add' := by
    intro z z'
    change Algebra.trace BinaryField K
        (c * fieldDet3 (Q x) (Q y) (Q (z + z'))) = _
    rw [Q.map_add, fieldDet3_add_third, mul_add, map_add]
  map_smul' := by
    intro a z
    change Algebra.trace BinaryField K
        (c * fieldDet3 (Q x) (Q y) (Q (a • z))) = _
    rw [Q.map_smul, fieldDet3_binary_smul_third]
    calc
      Algebra.trace BinaryField K
          (c * (algebraMap BinaryField K a * fieldDet3 (Q x) (Q y) (Q z))) =
          Algebra.trace BinaryField K
            (algebraMap BinaryField K a *
              (c * fieldDet3 (Q x) (Q y) (Q z))) := by
        congr 1
        ring
      _ = a • Algebra.trace BinaryField K
          (c * fieldDet3 (Q x) (Q y) (Q z)) := by
        rw [← Algebra.smul_def, map_smul]

set_option maxHeartbeats 2000000 in
private def qTraceDeterminantSecond
    {K : Type*} [Field K] [Finite K] [Algebra BinaryField K]
    {n : Nat} (Q : BinaryVector n ≃ₗ[BinaryField] FieldTriple K) (c : K)
    (x : BinaryVector n) :
    BinaryVector n →ₗ[BinaryField] (BinaryVector n →ₗ[BinaryField] BinaryField) where
  toFun y := qTraceDeterminantThird Q c x y
  map_add' := by
    intro y y'
    apply LinearMap.ext
    intro z
    change Algebra.trace BinaryField K
        (c * fieldDet3 (Q x) (Q (y + y')) (Q z)) = _
    rw [Q.map_add, fieldDet3_add_second, mul_add, map_add]
    simp [LinearMap.add_apply, qTraceDeterminantThird]
  map_smul' := by
    intro a y
    apply LinearMap.ext
    intro z
    change Algebra.trace BinaryField K
        (c * fieldDet3 (Q x) (Q (a • y)) (Q z)) = _
    rw [Q.map_smul, fieldDet3_binary_smul_second]
    calc
      Algebra.trace BinaryField K
          (c * (algebraMap BinaryField K a * fieldDet3 (Q x) (Q y) (Q z))) =
          Algebra.trace BinaryField K
            (algebraMap BinaryField K a *
              (c * fieldDet3 (Q x) (Q y) (Q z))) := by
        congr 1
        ring
      _ = a • Algebra.trace BinaryField K
          (c * fieldDet3 (Q x) (Q y) (Q z)) := by
        rw [← Algebra.smul_def, map_smul]

set_option maxHeartbeats 2000000 in
/-- The clean trace-determinant tensor specified by the manuscript's field
coordinates `Q` and coefficient `c`. Its three input slots are the original
physical binary input vectors. -/
def qTraceDeterminantTensor
    {K : Type*} [Field K] [Finite K] [Algebra BinaryField K]
    {n : Nat} (Q : BinaryVector n ≃ₗ[BinaryField] FieldTriple K) (c : K) :
    BinaryTensor n where
  toFun x := qTraceDeterminantSecond Q c x
  map_add' := by
    intro x x'
    apply LinearMap.ext
    intro y
    apply LinearMap.ext
    intro z
    change Algebra.trace BinaryField K
        (c * fieldDet3 (Q (x + x')) (Q y) (Q z)) = _
    rw [Q.map_add, fieldDet3_add_first, mul_add, map_add]
    simp [LinearMap.add_apply, qTraceDeterminantSecond, qTraceDeterminantThird]
  map_smul' := by
    intro a x
    apply LinearMap.ext
    intro y
    apply LinearMap.ext
    intro z
    change Algebra.trace BinaryField K
        (c * fieldDet3 (Q (a • x)) (Q y) (Q z)) = _
    rw [Q.map_smul, fieldDet3_binary_smul_first]
    calc
      Algebra.trace BinaryField K
          (c * (algebraMap BinaryField K a * fieldDet3 (Q x) (Q y) (Q z))) =
          Algebra.trace BinaryField K
            (algebraMap BinaryField K a *
              (c * fieldDet3 (Q x) (Q y) (Q z))) := by
        congr 1
        ring
      _ = a • Algebra.trace BinaryField K
          (c * fieldDet3 (Q x) (Q y) (Q z)) := by
        rw [← Algebra.smul_def, map_smul]

/-- The input promise for the observed model: its tensor is the canonical
Q-derived clean trace determinant plus the observed pullback of the hidden
defect tensor. This records the manuscript's model data explicitly; it makes
no claim that an algorithm constructs or verifies that promise. -/
def HasObservedTraceDeterminantDecomposition
    {K : Type*} [Field K] [Finite K] [Algebra BinaryField K]
    {n m : Nat} (Ctotal : BinaryTensor n) (E : BinaryTensor m)
    (u : BinaryVector n →ₗ[ZMod 2] BinaryVector m)
    (Q : BinaryVector n ≃ₗ[BinaryField] FieldTriple K) (c : K) : Prop :=
  Ctotal = physicalPerturbedTensor (qTraceDeterminantTensor Q c) E u

/-- The observed tensor equals its canonical clean model plus the supplied
hidden defect pullback, directly from the explicit input decomposition
promise. -/
theorem originalObservedTensor_eq_clean_plus_defect
    {K : Type*} [Field K] [Finite K] [Algebra BinaryField K]
    {n m : Nat} (Ctotal : BinaryTensor n) (E : BinaryTensor m)
    (u : BinaryVector n →ₗ[ZMod 2] BinaryVector m)
    (Q : BinaryVector n ≃ₗ[BinaryField] FieldTriple K) (c : K)
    (hmodel : HasObservedTraceDeterminantDecomposition Ctotal E u Q c) :
    Ctotal = qTraceDeterminantTensor Q c + pullback E u := by
  exact hmodel

/-- On a clean third slot, the complete observed contraction bilinear form is
the canonical Q-derived trace-determinant form. The only model premise is the
explicit clean-plus-defect decomposition above. -/
theorem originalObserved_bilinForm_eq_clean_on_coannihilator
    {K : Type*} [Field K] [Finite K] [Algebra BinaryField K]
    {n m : Nat} (Ctotal : BinaryTensor n) (E : BinaryTensor m)
    (u : BinaryVector n →ₗ[ZMod 2] BinaryVector m)
    (Q : BinaryVector n ≃ₗ[BinaryField] FieldTriple K) (c : K)
    (hmodel : HasObservedTraceDeterminantDecomposition Ctotal E u Q c)
    (z : BinaryVector n)
    (hz : u z ∈ (modeImage E).dualCoannihilator) :
    physicalThirdSlotBilinForm Ctotal z =
      physicalThirdSlotBilinForm (qTraceDeterminantTensor Q c) z := by
  rw [originalObservedTensor_eq_clean_plus_defect Ctotal E u Q c hmodel]
  exact physicalPerturbed_bilinForm_eq_clean_of_modeImage_coannihilator
    (qTraceDeterminantTensor Q c) E u z hz

/-- Full physical four-slot balance on the four observed words, with the first
two contraction arguments arbitrary. -/
def actualFourBilinearBalanced {s : Nat} (A : BinaryTensor (3 * s))
    (tape : FiveWordTape s)
    (T : Module.End (ZMod 2) (BinaryVector (3 * s))) : Prop :=
  ∀ i : Fin 4, ∀ x y : BinaryVector (3 * s),
    physicalThirdSlotBilinForm A (tape.1 i) (T x) y =
      physicalThirdSlotBilinForm A (tape.1 i) x (T y)

/-- Under the model's explicit C_total = C_clean + E input promise, the
original observed tensor has the same complete four-word physical balance
predicate as the Q-derived clean trace-determinant tensor. The actual good
tape event supplies each required E-mode-image coannihilator condition; no
balance condition is assumed. -/
theorem actual_good_tape_observed_four_balance_iff_clean
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Finite K]
    [CharP K 2] [Algebra BinaryField K] [FiniteDimensional BinaryField K]
    [Algebra (ZMod (ringChar K)) K]
    {s : Nat}
    (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K)
    (E : BinaryTensor (3 * s))
    (U : Submodule BinaryField (KTriple K))
    (b : (Fin 4 → FieldTriple K) → Module.Basis (Fin s) BinaryField K)
    (tape : FiveWordTape s)
    (htape : tape ∈ actualFiveGoodTapeSet K Q
      (modeImageSemanticCleanFieldSet Q E) U b)
    (Ctotal : BinaryTensor (3 * s)) (c : K)
    (hmodel : HasObservedTraceDeterminantDecomposition Ctotal E
      LinearMap.id Q c)
    (T : Module.End (ZMod 2) (BinaryVector (3 * s))) :
    actualFourBilinearBalanced Ctotal tape T ↔
      actualFourBilinearBalanced (qTraceDeterminantTensor Q c) tape T := by
  constructor
  · intro h i x y
    have hform := originalObserved_bilinForm_eq_clean_on_coannihilator
      Ctotal E LinearMap.id Q c hmodel (tape.1 i)
      (modeImage_actual_good_tape_words_clean Q E U b tape htape i)
    have hxy := h i x y
    rw [hform] at hxy
    exact hxy
  · intro h i x y
    have hform := originalObserved_bilinForm_eq_clean_on_coannihilator
      Ctotal E LinearMap.id Q c hmodel (tape.1 i)
      (modeImage_actual_good_tape_words_clean Q E U b tape htape i)
    rw [hform]
    exact h i x y

end

end CorruptedFieldRecovery
