import CorruptedFieldRecovery.S010ModeImageTraceTransport
import CorruptedFieldRecovery.S010CleanSupportCardinality
import CorruptedFieldRecovery.ProbabilityFiveTupleAssembly
import CorruptedFieldRecovery.ProbabilityActualTapeBridge
import Mathlib.Tactic

namespace CorruptedFieldRecovery

open Module

noncomputable section

/-- The semantic support subspace is obtained from the tensor's actual
physical mode image by the proved coordinate/trace dual equivalence. -/
def modeImageSemanticSupport {K : Type*} [Field K] [Finite K]
    [Algebra BinaryField K] [FiniteDimensional BinaryField K]
    {s : Nat}
    (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K)
    (E : BinaryTensor (3 * s)) : Submodule BinaryField (KTriple K) :=
  semanticSupportFromPhysical (K := K) Q (modeImage E)

/-- The finite field-coordinate clean set is the annihilator of the same
trace image of `modeImage E` used to define the translate-count support. -/
def modeImageSemanticCleanFieldSet {K : Type*} [Field K] [Finite K]
    [Fintype K] [DecidableEq K] [Algebra BinaryField K]
    [FiniteDimensional BinaryField K] {s : Nat}
    (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K)
    (E : BinaryTensor (3 * s)) : Finset (FieldTriple K) :=
  cleanSupportSet (K := K)
    (actualTraceSupportSubmodule (K := K) (modeImageSemanticSupport Q E))

/-- The physical tensor-clean event is exactly the pullback of the semantic
clean set. -/
theorem modeImage_physical_clean_iff
    {K : Type*} [Field K] [Finite K] [Fintype K] [DecidableEq K]
    [Algebra BinaryField K] [FiniteDimensional BinaryField K] {s : Nat}
    (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K)
    (E : BinaryTensor (3 * s)) (x : BinaryVector (3 * s)) :
    x ∈ (modeImage E).dualCoannihilator ↔
      Q x ∈ modeImageSemanticCleanFieldSet Q E := by
  have hobs := modeImage_clean_iff_observation_zero Q E x
  have hkernel := physicalSupportObservation_kernel_iff Q
    (actualTraceSupportSubmodule (K := K) (modeImageSemanticSupport Q E)) x
  constructor
  · intro hx
    have hz := hobs.mpr hx
    have hfield := hkernel.mp hz
    simpa [modeImageSemanticCleanFieldSet, cleanSupportSet] using hfield
  · intro hx
    have hfield : Q x ∈
        (actualTraceSupportSubmodule (K := K) (modeImageSemanticSupport Q E)).dualCoannihilator :=
      by simpa [modeImageSemanticCleanFieldSet, cleanSupportSet] using hx
    exact hobs.mp (hkernel.mpr hfield)

/-- The clean field-coordinate set has the exact coannihilator cardinality.
The semantic support rank is the rank of the preimage of the actual physical
mode image under the coordinate/trace dual equivalence. -/
theorem modeImageSemanticCleanFieldSet_card
    {K : Type*} [Field K] [Finite K] [Fintype K] [DecidableEq K]
    [Algebra BinaryField K] [FiniteDimensional BinaryField K] {s r : Nat}
    (hs : Module.finrank BinaryField K = s)
    (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K)
    (E : BinaryTensor (3 * s))
    (hr : Module.finrank BinaryField (modeImageSemanticSupport Q E) = r) :
    (modeImageSemanticCleanFieldSet Q E).card = 2 ^ (3 * s - r) := by
  let U := modeImageSemanticSupport Q E
  let W := actualTraceSupportSubmodule (K := K) U
  have hW : Module.finrank BinaryField W = r := by
    dsimp [W, actualTraceSupportSubmodule]
    let A := ((fieldTripleEquivPi K).restrictScalars BinaryField).symm
    let T := binaryFieldTripleTraceDualEquiv K
    change Module.finrank BinaryField
        (Submodule.map T.toLinearMap (Submodule.map A.toLinearMap U)) = r
    calc
      _ = Module.finrank BinaryField (Submodule.map A.toLinearMap U) :=
        T.finrank_map_eq _
      _ = Module.finrank BinaryField U := A.finrank_map_eq U
      _ = r := hr
  have hcard := cleanSupportSet_card K s r hs W hW
  simpa [modeImageSemanticCleanFieldSet, U, W] using hcard

private theorem card_field_eq_pow_finrank
    (K : Type*) [Field K] [Fintype K]
    [Algebra BinaryField K] [FiniteDimensional BinaryField K]
    (s : Nat) (hs : Module.finrank BinaryField K = s) :
    Fintype.card K = 2 ^ s := by
  rw [Module.card_eq_pow_finrank (K := BinaryField) (V := K), hs]
  simp [BinaryField]

/-- The existing dependent five-tuple count instantiated by the actual
physical tensor support and the matching semantic support U, then transported
to the actual independent-bit five-word tape. -/
theorem modeImage_actualFiveTape_count_lower
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    [Algebra BinaryField K] [FiniteDimensional BinaryField K] [Finite K]
    {s r : Nat} (hs : Module.finrank BinaryField K = s)
    (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K)
    (E : BinaryTensor (3 * s))
    (hr : Module.finrank BinaryField (modeImageSemanticSupport Q E) = r)
    (b : (Fin 4 → FieldTriple K) → Basis (Fin s) BinaryField K) :
    ((2 ^ (3 * s - r) - (nonGenerators K).card * (2 ^ s) ^ 2) *
      ((2 ^ (3 * s - r) - (2 ^ s) ^ 2) *
        ((2 ^ (3 * s - r) - 2 ^ s) * (2 ^ (3 * s - r) - 1)))) *
      (2 ^ s - ((∑ d ∈ properDegrees K, 2 ^ d) + (2 ^ (2 * r) - 1))) ≤
      (actualFiveGoodTapeSet K Q (modeImageSemanticCleanFieldSet Q E)
        (modeImageSemanticSupport Q E) b).card := by
  classical
  let U := modeImageSemanticSupport Q E
  let A := modeImageSemanticCleanFieldSet Q E
  have hA : A.card = 2 ^ (3 * s - r) :=
    modeImageSemanticCleanFieldSet_card hs Q E hr
  have hK : Fintype.card K = 2 ^ s := card_field_eq_pow_finrank K s hs
  have hsemantic := card_goodFiveTupleSigma_lower K A U b r hr
  rw [hA, hK] at hsemantic
  calc
    _ ≤ (goodFiveTupleSigma K A U b).card := hsemantic
    _ = (actualFiveGoodTapeSet K Q A U b).card := by
      symm
      exact card_actualFiveGoodTapeSet K Q A U b

end

end CorruptedFieldRecovery
