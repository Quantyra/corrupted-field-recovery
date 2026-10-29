import CorruptedFieldRecovery.Support
import CorruptedFieldRecovery.S010PhysicalSupportTransport
import Mathlib.Tactic

namespace CorruptedFieldRecovery

noncomputable section

/-- The field-coordinate support transported all the way to the actual
physical dual. -/
def fieldToPhysicalDualEquiv {K : Type*} [Field K] [Finite K]
    [Algebra BinaryField K] [FiniteDimensional BinaryField K]
    {s : Nat}
    (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K) :
    KTriple K ≃ₗ[BinaryField]
      Module.Dual BinaryField (BinaryVector (3 * s)) :=
  ((fieldTripleEquivPi K).restrictScalars BinaryField).symm.trans
    ((binaryFieldTripleTraceDualEquiv K).trans Q.dualMap)

/-- The semantic support subspace is the preimage of the actual physical
support module under the binary-linear coordinate/trace dual equivalence. -/
def semanticSupportFromPhysical {K : Type*} [Field K] [Finite K]
    [Algebra BinaryField K] [FiniteDimensional BinaryField K]
    {s : Nat}
    (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K)
    (P : Submodule BinaryField
      (Module.Dual BinaryField (BinaryVector (3 * s)))) :
    Submodule BinaryField (KTriple K) :=
  Submodule.map (fieldToPhysicalDualEquiv Q).symm.toLinearMap P

/-- Pushing the semantic U back through the coordinate trace map recovers
exactly the physical support module in field-dual coordinates. -/
theorem actualTraceSupportSubmodule_eq_physicalPullback
    {K : Type*} [Field K] [Finite K]
    [Algebra BinaryField K] [FiniteDimensional BinaryField K]
    {s : Nat}
    (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K)
    (P : Submodule BinaryField
      (Module.Dual BinaryField (BinaryVector (3 * s)))) :
    actualTraceSupportSubmodule (K := K)
      (semanticSupportFromPhysical (K := K) Q P) =
      Submodule.map Q.dualMap.symm.toLinearMap P := by
  let A := ((fieldTripleEquivPi K).restrictScalars BinaryField).symm
  let T := binaryFieldTripleTraceDualEquiv K
  let E := fieldToPhysicalDualEquiv Q
  change Submodule.map T.toLinearMap
      (Submodule.map A.toLinearMap (Submodule.map E.symm.toLinearMap P)) = _
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  apply congrArg (fun f :
      Module.Dual BinaryField (BinaryVector (3 * s)) →ₗ[BinaryField]
        Module.Dual BinaryField (FieldTriple K) => Submodule.map f P)
  apply LinearMap.ext
  intro p
  change T (A (E.symm p)) = Q.dualMap.symm p
  simp [A, T, E, fieldToPhysicalDualEquiv, LinearEquiv.trans_apply]

/-- For the manuscript's actual tensor support, the physical observation
kernel is its dual coannihilator, transported by Q. -/
theorem modeImage_clean_iff_observation_zero
    {K : Type*} [Field K] [Finite K]
    [Algebra BinaryField K] [FiniteDimensional BinaryField K]
    {s : Nat}
    (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K)
    (E : BinaryTensor (3 * s))
    (x : BinaryVector (3 * s)) :
    physicalSupportObservation Q
        (actualTraceSupportSubmodule (K := K)
          (semanticSupportFromPhysical (K := K) Q (modeImage E))) x = 0 ↔
      x ∈ (modeImage E).dualCoannihilator := by
  rw [physicalSupportObservation_kernel_iff]
  rw [actualTraceSupportSubmodule_eq_physicalPullback]
  have htransport (g : Module.Dual BinaryField (BinaryVector (3 * s))) :
      (Q.dualMap.symm g) (Q x) = g x := by
    have h := congrArg (fun f : Module.Dual BinaryField (BinaryVector (3 * s)) => f x)
      (Q.dualMap.apply_symm_apply g)
    simpa only [LinearEquiv.dualMap_apply] using h
  constructor
  · intro hx
    rw [Submodule.mem_dualCoannihilator] at hx ⊢
    intro g hg
    have hmem : Q.dualMap.symm g ∈
        Submodule.map Q.dualMap.symm.toLinearMap (modeImage E) :=
      ⟨g, hg, rfl⟩
    have hzero := hx (Q.dualMap.symm g) hmem
    calc
      g x = (Q.dualMap.symm g) (Q x) := (htransport g).symm
      _ = 0 := hzero
  · intro hx
    rw [Submodule.mem_dualCoannihilator] at hx ⊢
    intro f hf
    obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hf
    calc
      (Q.dualMap.symm g) (Q x) = g x := htransport g
      _ = 0 := hx g hg

end

end CorruptedFieldRecovery
