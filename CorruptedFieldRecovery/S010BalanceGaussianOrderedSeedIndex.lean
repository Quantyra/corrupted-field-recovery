import CorruptedFieldRecovery.S010BalanceGaussianRandomCoefficientSelection
import Mathlib.Data.List.NodupEquivFin

namespace CorruptedFieldRecovery

/-- The filtered free-column list contains no repeated coordinates because it
is a filter of the duplicate-free `List.ofFn` enumeration of `Fin`. -/
theorem actualBalanceGaussianRawFreeColumns_nodup {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s) :
    (actualBalanceGaussianRawFreeColumns raw tape).Nodup := by
  unfold actualBalanceGaussianRawFreeColumns
  apply List.Nodup.filter
  apply List.nodup_ofFn_ofInjective
  intro x y hxy
  exact hxy

/-- Membership in the actual ordered free-column filter is equivalent to the
pivot-subtype index used by the Gaussian basis proofs. -/
def actualBalanceGaussianRawFreeColumnMembershipEquiv {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s) :
    {column // column ∈ actualBalanceGaussianRawFreeColumns raw tape} ≃
      actualBalanceGaussianRawFreeIndex raw tape where
  toFun column :=
    ⟨column.1, of_decide_eq_true (List.mem_filter.mp column.2).2⟩
  invFun free :=
    ⟨free.1, List.mem_filter.mpr ⟨by
      simp, by
      simp [free.2]⟩⟩
  left_inv column := by
    apply Subtype.ext
    rfl
  right_inv free := by
    apply Subtype.ext
    rfl

/-- The order-preserving enumeration of the computed free-column list is a
computable equivalence from list positions to the scan's free-index subtype.
Forward evaluation uses `List.get`; the inverse locates a free column with
`idxOf`. No arbitrary choice of a finite-type ordering is used. -/
def actualBalanceGaussianRawFreeIndexListEquiv {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s) :
    Fin (actualBalanceGaussianRawFreeColumns raw tape).length ≃
      actualBalanceGaussianRawFreeIndex raw tape :=
  (List.Nodup.getEquiv (actualBalanceGaussianRawFreeColumns raw tape)
    (actualBalanceGaussianRawFreeColumns_nodup raw tape)).trans
      (actualBalanceGaussianRawFreeColumnMembershipEquiv raw tape)

/-- The actual free-column list length is the cardinality of its index subtype.
This bridges the executable enumeration to the finite type used by the basis
proofs. -/
theorem actualBalanceGaussianRawFreeColumns_length_eq_card {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s) :
    (actualBalanceGaussianRawFreeColumns raw tape).length =
      Fintype.card (actualBalanceGaussianRawFreeIndex raw tape) := by
  simpa using Fintype.card_congr
    (actualBalanceGaussianRawFreeIndexListEquiv raw tape)

/-- Given the actual cardinality result, use the concrete filtered-list order
to reindex s coefficient bits by the computed free columns. This is the
computable indexing step absent from the previous abstract cardinality-based
equivalence. -/
def actualBalanceGaussianRawFreeIndexFinEquiv {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s)
    (hcard : Fintype.card (actualBalanceGaussianRawFreeIndex raw tape) = s) :
    Fin s ≃ actualBalanceGaussianRawFreeIndex raw tape :=
  (finCongr
    ((actualBalanceGaussianRawFreeColumns_length_eq_card raw tape).trans hcard)).symm.trans
      (actualBalanceGaussianRawFreeIndexListEquiv raw tape)

/-- Under the good-event/model hypotheses and field-dimension s, the actual
filtered free-column list has length s. This specializes the previous
Q-scalar range cardinality argument to the concrete scan output. -/
theorem actualBalanceGaussianRawFreeColumns_length_eq_s
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
    (actualBalanceGaussianRawFreeColumns raw tape).length = s := by
  rw [actualBalanceGaussianRawFreeColumns_length_eq_card]
  exact actualBalanceGaussianRawFreeIndex_card_eq
    Q E U b raw tape htape c hc hmodel hsize hK

/-- The ordered-list index equivalence is available from the actual good-event
and model assumptions. It is assembled from `Fin` casts and the executable
`get`/`idxOf` list equivalence above. -/
def actualBalanceGaussianRawGoodEventFreeIndexFinEquiv
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
    Fin s ≃ actualBalanceGaussianRawFreeIndex raw tape := by
  exact actualBalanceGaussianRawFreeIndexFinEquiv raw tape
    (actualBalanceGaussianRawFreeIndex_card_eq
      Q E U b raw tape htape c hc hmodel hsize hK)

/-- The actual array-list seed selection computes the corresponding linear
combination of the emitted free-column candidates in list order. Its list
indexing is executable; the field-semantic equivalence is proved separately. -/
noncomputable def actualBalanceGaussianArrayFlagSelectBySeed {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s)
    (hcard : Fintype.card (actualBalanceGaussianRawFreeIndex raw tape) = s)
    (seed : Fin s → BinaryField) :
    Module.End BinaryField (BinaryVector (3 * s)) :=
  actualBalanceGaussianRawWeightedCombination raw tape
    (fun free => seed
      ((actualBalanceGaussianRawFreeIndexFinEquiv raw tape hcard).symm free))

/-- With the exact free-index cardinality, the seed-to-scalar map is a
bijection. Thus uniform s-bit coefficient seeds select every scalar action
exactly once. This still includes scalars that fail the subsequent
irreducibility/generator test. -/
theorem actualBalanceGaussianArrayFlagSeedScalar_bijective
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
    Function.Bijective (fun seed : Fin s → BinaryField =>
      actualBalanceGaussianQScalarParameter Q
        (actualBalanceGaussianArrayFlagSelectBySeed raw tape
          (actualBalanceGaussianRawFreeIndex_card_eq
            Q E U b raw tape htape c hc hmodel hsize hK) seed)) := by
  let hindex := actualBalanceGaussianRawGoodEventFreeIndexFinEquiv
    Q E U b raw tape htape c hc hmodel hsize hK
  let hequiv := actualBalanceGaussianRawSeedEquivField
    Q E U b raw tape htape c hc hmodel hsize hindex
  constructor
  · intro x y hxy
    apply hequiv.injective
    change actualBalanceGaussianQScalarParameter Q
        (actualBalanceGaussianRawWeightedCombination raw tape
          (fun free => x (hindex.symm free))) =
      actualBalanceGaussianQScalarParameter Q
        (actualBalanceGaussianRawWeightedCombination raw tape
          (fun free => y (hindex.symm free))) at hxy
    exact hxy
  · intro k
    obtain ⟨seed, hseed⟩ := hequiv.surjective k
    exact ⟨seed, hseed⟩

end CorruptedFieldRecovery