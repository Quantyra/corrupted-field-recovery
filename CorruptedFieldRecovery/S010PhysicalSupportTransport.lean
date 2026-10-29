import CorruptedFieldRecovery.ProperSubfieldCounts
import CorruptedFieldRecovery.BinaryTensor
import CorruptedFieldRecovery.FourContractions
import CorruptedFieldRecovery.TranslateScalarCounts
import CorruptedFieldRecovery.S010CleanSupportCardinality
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

namespace CorruptedFieldRecovery

noncomputable section

/-- The coordinate trace pairing, formed over the manuscript's actual binary
coefficient field. -/
def binaryFieldTripleTraceCovector {K : Type*} [Field K]
    [Algebra BinaryField K] (a : FieldTriple K) :
    Module.Dual BinaryField (FieldTriple K) :=
  { toFun := fun x =>
      Algebra.trace BinaryField K (a.1 * x.1) +
        Algebra.trace BinaryField K (a.2.1 * x.2.1) +
        Algebra.trace BinaryField K (a.2.2 * x.2.2)
    map_add' := by
      intro x y
      simp only [Prod.fst_add, Prod.snd_add, mul_add, map_add]
      abel_nf
    map_smul' := by
      intro r x
      simp only [Prod.smul_fst, Prod.smul_snd]
      rw [show a.1 * (r • x.1) = r • (a.1 * x.1) by
          rw [Algebra.smul_def, Algebra.smul_def]
          ring,
        show a.2.1 * (r • x.2.1) = r • (a.2.1 * x.2.1) by
          rw [Algebra.smul_def, Algebra.smul_def]
          ring,
        show a.2.2 * (r • x.2.2) = r • (a.2.2 * x.2.2) by
          rw [Algebra.smul_def, Algebra.smul_def]
          ring]
      simp only [map_smul, RingHom.id_apply]
      simp
      ring }

private theorem binaryTracePairing_nondegenerate {K : Type*} [Field K]
    [Finite K] [Algebra BinaryField K] [FiniteDimensional BinaryField K]
    {a : K} (ha : a ≠ 0) :
    ∃ b : K, Algebra.trace BinaryField K (a * b) ≠ 0 := by
  have htr := (traceForm_nondegenerate BinaryField K).1 a
  simp_rw [Algebra.traceForm_apply] at htr
  by_contra! hf
  exact ha (htr hf)

private theorem binaryFieldTripleTraceCovector_eq_zero_iff
    {K : Type*} [Field K] [Finite K] [Algebra BinaryField K]
    [FiniteDimensional BinaryField K] (a : FieldTriple K) :
    binaryFieldTripleTraceCovector a = 0 ↔ a = 0 := by
  constructor
  · intro h
    have h0 : a.1 = 0 := by
      by_contra ha
      obtain ⟨y, hy⟩ := binaryTracePairing_nondegenerate ha
      have hz := congrArg (fun f : Module.Dual BinaryField (FieldTriple K) =>
        f (y, 0, 0)) h
      simp [binaryFieldTripleTraceCovector] at hz
      exact hy (by simpa only [one_mul] using hz)
    have h1 : a.2.1 = 0 := by
      by_contra ha
      obtain ⟨y, hy⟩ := binaryTracePairing_nondegenerate ha
      have hz := congrArg (fun f : Module.Dual BinaryField (FieldTriple K) =>
        f (0, y, 0)) h
      simp [binaryFieldTripleTraceCovector] at hz
      exact hy (by simpa only [one_mul] using hz)
    have h2 : a.2.2 = 0 := by
      by_contra ha
      obtain ⟨y, hy⟩ := binaryTracePairing_nondegenerate ha
      have hz := congrArg (fun f : Module.Dual BinaryField (FieldTriple K) =>
        f (0, 0, y)) h
      simp [binaryFieldTripleTraceCovector] at hz
      exact hy (by simpa only [one_mul] using hz)
    ext <;> assumption
  · rintro rfl
    apply LinearMap.ext
    intro x
    simp [binaryFieldTripleTraceCovector]

/-- The binary-field trace pairing identifies the coordinate triple with its
full binary dual. -/
noncomputable def binaryFieldTripleTraceDualEquiv (K : Type*) [Field K]
    [Finite K] [Algebra BinaryField K] [FiniteDimensional BinaryField K] :
    FieldTriple K ≃ₗ[BinaryField]
      Module.Dual BinaryField (FieldTriple K) := by
  let f : FieldTriple K →ₗ[BinaryField]
      Module.Dual BinaryField (FieldTriple K) := {
    toFun := binaryFieldTripleTraceCovector
    map_add' := by
      intro a b
      apply LinearMap.ext
      intro x
      rcases x with ⟨x0, x1, x2⟩
      change
        Algebra.trace BinaryField K ((a.1 + b.1) * x0) +
            Algebra.trace BinaryField K ((a.2.1 + b.2.1) * x1) +
            Algebra.trace BinaryField K ((a.2.2 + b.2.2) * x2) =
          (Algebra.trace BinaryField K (a.1 * x0) +
            Algebra.trace BinaryField K (a.2.1 * x1) +
            Algebra.trace BinaryField K (a.2.2 * x2)) +
          (Algebra.trace BinaryField K (b.1 * x0) +
            Algebra.trace BinaryField K (b.2.1 * x1) +
            Algebra.trace BinaryField K (b.2.2 * x2))
      rw [add_mul, map_add, add_mul, map_add, add_mul, map_add]
      abel_nf
    map_smul' := by
      intro r a
      apply LinearMap.ext
      intro x
      rcases x with ⟨x0, x1, x2⟩
      change
        Algebra.trace BinaryField K ((r • a.1) * x0) +
            Algebra.trace BinaryField K ((r • a.2.1) * x1) +
            Algebra.trace BinaryField K ((r • a.2.2) * x2) =
          r • (Algebra.trace BinaryField K (a.1 * x0) +
            Algebra.trace BinaryField K (a.2.1 * x1) +
            Algebra.trace BinaryField K (a.2.2 * x2))
      rw [show (r • a.1) * x0 = r • (a.1 * x0) by
          rw [Algebra.smul_def, Algebra.smul_def]
          ring,
        show (r • a.2.1) * x1 = r • (a.2.1 * x1) by
          rw [Algebra.smul_def, Algebra.smul_def]
          ring,
        show (r • a.2.2) * x2 = r • (a.2.2 * x2) by
          rw [Algebra.smul_def, Algebra.smul_def]
          ring]
      simp only [map_smul]
      simp
      ring }
  have hinj : Function.Injective f := by
    intro a b hab
    have hz : f (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have hcoord := (binaryFieldTripleTraceCovector_eq_zero_iff (a - b)).mp hz
    exact sub_eq_zero.mp hcoord
  exact LinearMap.linearEquivOfInjective f hinj (by simp)

/-- Transport the semantic support subspace through the binary-field trace
equivalence. This uses the same U as the translate count. -/
def actualTraceSupportSubmodule {K : Type*} [Field K] [Finite K]
    [Algebra BinaryField K] [FiniteDimensional BinaryField K]
    (U : Submodule BinaryField (KTriple K)) :
    Submodule BinaryField (Module.Dual BinaryField (FieldTriple K)) :=
  Submodule.map (binaryFieldTripleTraceDualEquiv K).toLinearMap
    (Submodule.map ((fieldTripleEquivPi K).restrictScalars BinaryField).symm.toLinearMap U)

/-- Observe every trace-dual support coordinate. -/
def physicalSupportObservation {K : Type*} [Field K] [Finite K]
    [Algebra BinaryField K] [FiniteDimensional BinaryField K]
    {s : Nat}
    (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K)
    (W : Submodule BinaryField (Module.Dual BinaryField (FieldTriple K))) :
    BinaryVector (3 * s) →ₗ[BinaryField] Module.Dual BinaryField W :=
  (W.subtype.dualMap).comp
    ((Module.evalEquiv BinaryField (FieldTriple K)).toLinearMap.comp
      Q.toLinearMap)

theorem physicalSupportObservation_surjective {K : Type*} [Field K]
    [Finite K] [Algebra BinaryField K] [FiniteDimensional BinaryField K]
    {s : Nat}
    (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K)
    (W : Submodule BinaryField (Module.Dual BinaryField (FieldTriple K))) :
    Function.Surjective (physicalSupportObservation Q W) := by
  apply Function.Surjective.comp
    (LinearMap.dualMap_surjective_of_injective W.subtype_injective)
  exact (Module.evalEquiv BinaryField (FieldTriple K)).surjective.comp Q.surjective

theorem physicalSupportObservation_kernel_iff {K : Type*} [Field K]
    [Finite K] [Algebra BinaryField K] [FiniteDimensional BinaryField K]
    {s : Nat}
    (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K)
    (W : Submodule BinaryField (Module.Dual BinaryField (FieldTriple K)))
    (x : BinaryVector (3 * s)) :
    physicalSupportObservation Q W x = 0 ↔ Q x ∈ W.dualCoannihilator := by
  rw [Submodule.mem_dualCoannihilator]
  constructor
  · intro h f hf
    have heval := congrArg (fun g : Module.Dual BinaryField W => g ⟨f, hf⟩) h
    simpa [physicalSupportObservation, LinearMap.comp_apply,
      LinearMap.dualMap_apply, Module.evalEquiv_apply, Module.Dual.eval_apply] using heval
  · intro h
    apply LinearMap.ext
    intro f
    exact h f.1 f.2

end

end CorruptedFieldRecovery
