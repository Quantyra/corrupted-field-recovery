import CorruptedFieldRecovery.S010BalanceGaussianScalarRangeBridge
import CorruptedFieldRecovery.S010BalanceGaussianArrayFlagGoodEventNonempty

namespace CorruptedFieldRecovery

open scoped Classical

/-- The finite index type of free columns in the deterministic raw matrix scan. -/
abbrev actualBalanceGaussianRawFreeIndex {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s) :=
  balanceGaussianFreeIndex (actualBalanceGaussianRawScan raw tape).2

/-- Choose an arbitrary coefficient for every computed free-column basis
vector and form their linear combination in the physical endomorphism space.
This is the faithful algebraic operation corresponding to the manuscript's
random selection from the entire balance space. -/
noncomputable def actualBalanceGaussianRawWeightedCombination {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s)
    (weights : actualBalanceGaussianRawFreeIndex raw tape → BinaryField) :
    Module.End BinaryField (BinaryVector (3 * s)) :=
  ∑ free : actualBalanceGaussianRawFreeIndex raw tape,
    weights free • actualBalanceGaussianRawCandidateFamily raw tape free

/-- A weighted combination of the computed candidates lies in the actual
Q-scalar balance range on a genuine good tape satisfying the explicit model
promise. -/
theorem actualBalanceGaussianRawWeightedCombination_mem_qScalarRange
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Finite K]
    [CharP K 2] [Algebra BinaryField K] [FiniteDimensional BinaryField K]
    [Algebra (ZMod (ringChar K)) K]
    {s : Nat}
    (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K)
    (E : BinaryTensor (3 * s))
    (U : Submodule BinaryField (KTriple K))
    (b : (Fin 4 → FieldTriple K) → Module.Basis (Fin s) BinaryField K)
    (raw : RawCoefficientArray) (tape : FiveWordTape s)
    (htape : tape ∈ actualFiveGoodTapeSet K Q
      (modeImageSemanticCleanFieldSet Q E) U b)
    (c : K) (hc : c ≠ 0)
    (hmodel : HasObservedTraceDeterminantDecomposition
      (decodeRawArray (n := 3 * s) raw) E LinearMap.id Q c)
    (_hsize : raw.size = (3 * s) * (3 * s) * (3 * s))
    (weights : actualBalanceGaussianRawFreeIndex raw tape → BinaryField) :
    actualBalanceGaussianRawWeightedCombination raw tape weights ∈
      qScalarConjugateEndRange Q := by
  let hiff := actual_good_tape_observed_balance_iff_mem_qScalarConjugateEndRange
    Q E U b tape htape (decodeRawArray (n := 3 * s) raw) c hmodel hc
  have hcandidate : ∀ free : actualBalanceGaussianRawFreeIndex raw tape,
      actualBalanceGaussianRawCandidateFamily raw tape free ∈
        qScalarConjugateEndRange Q := by
    intro free
    exact (hiff (actualBalanceGaussianRawCandidateFamily raw tape free)).mp
      (actualBalanceGaussianRawCandidate_balanced raw tape free)
  change (∑ free : actualBalanceGaussianRawFreeIndex raw tape,
      weights free • actualBalanceGaussianRawCandidateFamily raw tape free) ∈ _
  apply Submodule.sum_smul_mem
  intro free hfree
  exact hcandidate free

/-- The candidate combination map is injective: its columns are the linearly
independent free-column family proved from the full scan. -/
theorem actualBalanceGaussianRawWeightedCombination_injective
    {s : Nat} (raw : RawCoefficientArray) (tape : FiveWordTape s) :
    Function.Injective
      (actualBalanceGaussianRawWeightedCombination raw tape) := by
  classical
  let Free := actualBalanceGaussianRawFreeIndex raw tape
  let family := actualBalanceGaussianRawCandidateFamily raw tape
  have hLI := actualBalanceGaussianRawCandidateFamily_linearIndependent raw tape
  rw [Fintype.linearIndependent_iff] at hLI
  intro x y hxy
  have hval : actualBalanceGaussianRawWeightedCombination raw tape x =
      actualBalanceGaussianRawWeightedCombination raw tape y :=
    congrArg Subtype.val hxy
  have hrel : (∑ free : Free, (x free - y free) • family free) = 0 := by
    calc
      (∑ free : Free, (x free - y free) • family free) =
          (∑ free : Free, x free • family free) -
            (∑ free : Free, y free • family free) := by
              rw [Finset.sum_sub_distrib]
              simp [sub_smul]
      _ = 0 := by
        simpa [actualBalanceGaussianRawWeightedCombination, Free, family] using
          sub_eq_zero.mpr hval
  have hzero : (fun free : Free => x free - y free) = 0 :=
    hLI (fun free => x free - y free) hrel
  funext free
  have hcoord := congrFun hzero free
  exact sub_eq_zero.mp hcoord

/-- Every member of the Q-scalar balance range is a combination of the
computed free-column candidates. This is the full raw-scan reconstruction
statement specialized to the promised good-event balance space. -/
theorem actualBalanceGaussianRawWeightedCombination_surjective
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Finite K]
    [CharP K 2] [Algebra BinaryField K] [FiniteDimensional BinaryField K]
    [Algebra (ZMod (ringChar K)) K]
    {s : Nat}
    (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K)
    (E : BinaryTensor (3 * s))
    (U : Submodule BinaryField (KTriple K))
    (b : (Fin 4 → FieldTriple K) → Module.Basis (Fin s) BinaryField K)
    (raw : RawCoefficientArray) (tape : FiveWordTape s)
    (htape : tape ∈ actualFiveGoodTapeSet K Q
      (modeImageSemanticCleanFieldSet Q E) U b)
    (c : K) (hc : c ≠ 0)
    (hmodel : HasObservedTraceDeterminantDecomposition
      (decodeRawArray (n := 3 * s) raw) E LinearMap.id Q c)
    (hsize : raw.size = (3 * s) * (3 * s) * (3 * s)) :
    ∀ T : qScalarConjugateEndRange Q,
      ∃ weights : actualBalanceGaussianRawFreeIndex raw tape → BinaryField,
        actualBalanceGaussianRawWeightedCombination raw tape weights = T := by
  intro T
  have hspan := actualBalanceGaussianRawBasis_spans_QScalarRange
    Q E U b raw tape htape c hc hmodel hsize T.1
  refine ⟨fun free => actualBalanceGaussianInputCoordinates T.1 free.1, ?_⟩
  apply Subtype.ext
  change (∑ free : actualBalanceGaussianRawFreeIndex raw tape,
      actualBalanceGaussianInputCoordinates T.1 free.1 •
        actualBalanceGaussianRawCandidateFamily raw tape free) = T.1
  exact hspan.mpr T.2 |>.symm

/-- A bijection from all coefficient functions on the free-column family to
the Q-scalar balance space. Thus, once the family is known to have size s,
coefficient vectors enumerate that whole space without bias. -/
noncomputable def actualBalanceGaussianRawWeightsEquivQScalarRange
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Finite K]
    [CharP K 2] [Algebra BinaryField K] [FiniteDimensional BinaryField K]
    [Algebra (ZMod (ringChar K)) K]
    {s : Nat}
    (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K)
    (E : BinaryTensor (3 * s))
    (U : Submodule BinaryField (KTriple K))
    (b : (Fin 4 → FieldTriple K) → Module.Basis (Fin s) BinaryField K)
    (raw : RawCoefficientArray) (tape : FiveWordTape s)
    (htape : tape ∈ actualFiveGoodTapeSet K Q
      (modeImageSemanticCleanFieldSet Q E) U b)
    (c : K) (hc : c ≠ 0)
    (hmodel : HasObservedTraceDeterminantDecomposition
      (decodeRawArray (n := 3 * s) raw) E LinearMap.id Q c)
    (hsize : raw.size = (3 * s) * (3 * s) * (3 * s)) :
    (actualBalanceGaussianRawFreeIndex raw tape → BinaryField) ≃
      qScalarConjugateEndRange Q :=
  Equiv.ofBijective
    (fun weights =>
      ⟨actualBalanceGaussianRawWeightedCombination raw tape weights,
        actualBalanceGaussianRawWeightedCombination_mem_qScalarRange
          Q E U b raw tape htape c hc hmodel hsize weights⟩)
    ⟨by
        intro x y hxy
        apply actualBalanceGaussianRawWeightedCombination_injective raw tape
        exact congrArg Subtype.val hxy,
      actualBalanceGaussianRawWeightedCombination_surjective
        Q E U b raw tape htape c hc hmodel hsize⟩

/-- The scan's free-coordinate type has cardinality s whenever the coefficient
field has binary dimension s. The proof compares cardinalities through the
computed-basis/Q-range bijection; it does not assert that a list-order
reindexing has already been implemented. -/
theorem actualBalanceGaussianRawFreeIndex_card_eq
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Finite K]
    [CharP K 2] [Algebra BinaryField K] [FiniteDimensional BinaryField K]
    [Algebra (ZMod (ringChar K)) K]
    {s : Nat}
    (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K)
    (E : BinaryTensor (3 * s))
    (U : Submodule BinaryField (KTriple K))
    (b : (Fin 4 → FieldTriple K) → Module.Basis (Fin s) BinaryField K)
    (raw : RawCoefficientArray) (tape : FiveWordTape s)
    (htape : tape ∈ actualFiveGoodTapeSet K Q
      (modeImageSemanticCleanFieldSet Q E) U b)
    (c : K) (hc : c ≠ 0)
    (hmodel : HasObservedTraceDeterminantDecomposition
      (decodeRawArray (n := 3 * s) raw) E LinearMap.id Q c)
    (hsize : raw.size = (3 * s) * (3 * s) * (3 * s))
    (hK : Module.finrank BinaryField K = s) :
    Fintype.card (actualBalanceGaussianRawFreeIndex raw tape) = s := by
  let e := actualBalanceGaussianRawWeightsEquivQScalarRange
    Q E U b raw tape htape c hc hmodel hsize
  have hcard : Nat.card (actualBalanceGaussianRawFreeIndex raw tape → BinaryField) =
      Nat.card (qScalarConjugateEndRange Q) := Nat.card_congr e
  have hfun : Nat.card (actualBalanceGaussianRawFreeIndex raw tape → BinaryField) =
      2 ^ Nat.card (actualBalanceGaussianRawFreeIndex raw tape) := by
    rw [Nat.card_fun]
    simp [BinaryField]
  have hrange : Nat.card (qScalarConjugateEndRange Q) = 2 ^ s := by
    rw [Module.natCard_eq_pow_finrank (K := BinaryField)
      (V := qScalarConjugateEndRange Q), qScalarConjugateEndRange_finrank Q, hK]
    simp [BinaryField]
  have hpow : 2 ^ Nat.card
      (actualBalanceGaussianRawFreeIndex raw tape) = 2 ^ s :=
    hfun.symm.trans (hcard.trans hrange)
  have hfinal : Nat.card (actualBalanceGaussianRawFreeIndex raw tape) = s :=
    Nat.pow_right_injective (by decide : 2 ≤ 2) hpow
  rw [← Nat.card_eq_fintype_card]
  exact hfinal

/-- Given an explicit enumeration equivalence from s bit positions to the
computed free columns, uniform s-bit coefficient seeds biject onto the entire
Q-scalar balance space. The equivalence is a parameter so no noncomputable
choice of ordering is hidden in the selector. -/
noncomputable def actualBalanceGaussianRawSeedEquivQScalarRange
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Finite K]
    [CharP K 2] [Algebra BinaryField K] [FiniteDimensional BinaryField K]
    [Algebra (ZMod (ringChar K)) K]
    {s : Nat}
    (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K)
    (E : BinaryTensor (3 * s))
    (U : Submodule BinaryField (KTriple K))
    (b : (Fin 4 → FieldTriple K) → Module.Basis (Fin s) BinaryField K)
    (raw : RawCoefficientArray) (tape : FiveWordTape s)
    (htape : tape ∈ actualFiveGoodTapeSet K Q
      (modeImageSemanticCleanFieldSet Q E) U b)
    (c : K) (hc : c ≠ 0)
    (hmodel : HasObservedTraceDeterminantDecomposition
      (decodeRawArray (n := 3 * s) raw) E LinearMap.id Q c)
    (hsize : raw.size = (3 * s) * (3 * s) * (3 * s))
    (hindex : Fin s ≃ actualBalanceGaussianRawFreeIndex raw tape) :
    (Fin s → BinaryField) ≃ qScalarConjugateEndRange Q := by
  let ew := actualBalanceGaussianRawWeightsEquivQScalarRange
    Q E U b raw tape htape c hc hmodel hsize
  let f := fun (seed : Fin s → BinaryField) =>
    ew (fun free => seed (hindex.symm free))
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      have hw := ew.injective h
      funext i
      simpa [f] using congrFun hw (hindex i)
    · intro T
      let w := ew.symm T
      refine ⟨fun i => w (hindex i), ?_⟩
      simp [f, w]
  exact Equiv.ofBijective f hf

/-- Inverting Q-conjugation recovers the unique field scalar. Composing this
with the seed equivalence shows that uniform s-bit coefficient seeds index K
bijectively under hindex. -/
noncomputable def actualBalanceGaussianRawSeedEquivField
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Finite K]
    [CharP K 2] [Algebra BinaryField K] [FiniteDimensional BinaryField K]
    [Algebra (ZMod (ringChar K)) K]
    {s : Nat}
    (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K)
    (E : BinaryTensor (3 * s))
    (U : Submodule BinaryField (KTriple K))
    (b : (Fin 4 → FieldTriple K) → Module.Basis (Fin s) BinaryField K)
    (raw : RawCoefficientArray) (tape : FiveWordTape s)
    (htape : tape ∈ actualFiveGoodTapeSet K Q
      (modeImageSemanticCleanFieldSet Q E) U b)
    (c : K) (hc : c ≠ 0)
    (hmodel : HasObservedTraceDeterminantDecomposition
      (decodeRawArray (n := 3 * s) raw) E LinearMap.id Q c)
    (hsize : raw.size = (3 * s) * (3 * s) * (3 * s))
    (hindex : Fin s ≃ actualBalanceGaussianRawFreeIndex raw tape) :
    (Fin s → BinaryField) ≃ K := by
  let eRange := actualBalanceGaussianRawSeedEquivQScalarRange
    Q E U b raw tape htape c hc hmodel hsize hindex
  let eScalar : qScalarConjugateEndRange Q ≃ K :=
    { toFun := actualBalanceGaussianQScalarParameter Q
      invFun := fun k => ⟨qScalarConjugateLinearMap Q k, ⟨k, rfl⟩⟩
      left_inv := by
        intro T
        apply Subtype.ext
        exact actualBalanceGaussianQScalarParameter_spec Q T.2
      right_inv := by
        intro k
        apply qScalarConjugateLinearMap_injective Q
        exact actualBalanceGaussianQScalarParameter_spec Q
          ⟨qScalarConjugateLinearMap Q k, ⟨k, rfl⟩⟩ }
  exact eRange.trans eScalar

/-- The coefficient-combination sampler covers every scalar action exactly
once. A later irreducibility/minimal-polynomial test is still required: the
bijection includes 1 and other nongenerators, so it is not an unconditional
constructor-success theorem. -/
theorem actualBalanceGaussianRawSeedEquivField_bijective
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Finite K]
    [CharP K 2] [Algebra BinaryField K] [FiniteDimensional BinaryField K]
    [Algebra (ZMod (ringChar K)) K]
    {s : Nat}
    (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K)
    (E : BinaryTensor (3 * s))
    (U : Submodule BinaryField (KTriple K))
    (b : (Fin 4 → FieldTriple K) → Module.Basis (Fin s) BinaryField K)
    (raw : RawCoefficientArray) (tape : FiveWordTape s)
    (htape : tape ∈ actualFiveGoodTapeSet K Q
      (modeImageSemanticCleanFieldSet Q E) U b)
    (c : K) (hc : c ≠ 0)
    (hmodel : HasObservedTraceDeterminantDecomposition
      (decodeRawArray (n := 3 * s) raw) E LinearMap.id Q c)
    (hsize : raw.size = (3 * s) * (3 * s) * (3 * s))
    (hindex : Fin s ≃ actualBalanceGaussianRawFreeIndex raw tape) :
    Function.Bijective
      (actualBalanceGaussianRawSeedEquivField
        Q E U b raw tape htape c hc hmodel hsize hindex) := by
  exact (actualBalanceGaussianRawSeedEquivField
    Q E U b raw tape htape c hc hmodel hsize hindex).bijective

end CorruptedFieldRecovery