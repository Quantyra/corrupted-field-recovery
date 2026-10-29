import CorruptedFieldRecovery.FourContractions
import CorruptedFieldRecovery.Bridge

/-! The manuscript's trace-coordinate identification of a finite-field
three-space with its binary dual, and the scalar-action identity under that
identification. -/

namespace CorruptedFieldRecovery

noncomputable section

variable (K : Type*) [Field K] [Finite K]
variable [Algebra (ZMod (ringChar K)) K]

local notation "F" => ZMod (ringChar K)

/-- The binary covector represented by a coordinate triple, using the
coordinatewise finite-field trace pairing. -/
def fieldTripleTraceCovector (a : FieldTriple K) :
    Module.Dual F (FieldTriple K) :=
  { toFun := fun x =>
      Algebra.trace F K (a.1 * x.1) +
        Algebra.trace F K (a.2.1 * x.2.1) +
        Algebra.trace F K (a.2.2 * x.2.2)
    map_add' := by
      intro x y
      simp only [Prod.fst_add, Prod.snd_add, mul_add, map_add]
      abel
    map_smul' := by
      intro r x
      simp only [Prod.smul_fst, Prod.smul_snd]
      rw [show (a.1 * (r • x.1)) = r • (a.1 * x.1) by
        rw [Algebra.smul_def, Algebra.smul_def]
        ring,
        show (a.2.1 * (r • x.2.1)) = r • (a.2.1 * x.2.1) by
          rw [Algebra.smul_def, Algebra.smul_def]
          ring,
        show (a.2.2 * (r • x.2.2)) = r • (a.2.2 * x.2.2) by
          rw [Algebra.smul_def, Algebra.smul_def]
          ring]
      simp only [map_smul, RingHom.id_apply]
      simp
      ring }

/-- Multiplication by `t` on the physical three-space, regarded as a linear
map over the binary prime field. -/
def fieldTripleScalarAction (t : K) : FieldTriple K →ₗ[F] FieldTriple K where
  toFun := fun x => t • x
  map_add' := by intro x y; exact smul_add t x y
  map_smul' := by
    intro r x
    ext <;> simp

/-- The coordinatewise trace pairing is nondegenerate: only the zero
coordinate triple induces the zero covector. -/
theorem fieldTripleTraceCovector_eq_zero_iff (a : FieldTriple K) :
    fieldTripleTraceCovector K a = 0 ↔ a = 0 := by
  constructor
  · intro h
    have h0 : a.1 = 0 := by
      by_contra ha
      obtain ⟨y, hy⟩ := tracePairing_nondegenerate K 1 (by norm_num) a.1 ha
      have hz := congrArg (fun f : Module.Dual F (FieldTriple K) => f (y, 0, 0)) h
      simp [fieldTripleTraceCovector] at hz
      exact hy (by simpa only [one_mul] using hz)
    have h1 : a.2.1 = 0 := by
      by_contra ha
      obtain ⟨y, hy⟩ := tracePairing_nondegenerate K 1 (by norm_num) a.2.1 ha
      have hz := congrArg (fun f : Module.Dual F (FieldTriple K) => f (0, y, 0)) h
      simp [fieldTripleTraceCovector] at hz
      exact hy (by simpa only [one_mul] using hz)
    have h2 : a.2.2 = 0 := by
      by_contra ha
      obtain ⟨y, hy⟩ := tracePairing_nondegenerate K 1 (by norm_num) a.2.2 ha
      have hz := congrArg (fun f : Module.Dual F (FieldTriple K) => f (0, 0, y)) h
      simp [fieldTripleTraceCovector] at hz
      exact hy (by simpa only [one_mul] using hz)
    ext <;> assumption
  · rintro rfl
    apply LinearMap.ext
    intro x
    simp [fieldTripleTraceCovector]

omit [Finite K] in
/-- Under the trace-coordinate identification, the dual map of scalar
multiplication is scalar multiplication on the coordinate triple. -/
theorem dualMap_fieldTripleScalarAction_trace
    (t : K) (a : FieldTriple K) :
    (fieldTripleScalarAction K t).dualMap (fieldTripleTraceCovector K a) =
      fieldTripleTraceCovector K (t • a) := by
  apply LinearMap.ext
  intro x
  change fieldTripleTraceCovector K a ((fieldTripleScalarAction K t) x) = _
  rcases x with ⟨x₀, x₁, x₂⟩
  simp [fieldTripleTraceCovector, fieldTripleScalarAction,
    Algebra.smul_def, mul_left_comm, mul_comm]

omit [Finite K] in
/-- Consequently, the trace-coordinate image of any support set is carried
by the actual dual action exactly as the manuscript's scalar translate. -/
theorem traceCoordinates_dualMap_mem_iff
    (t : K) (a : FieldTriple K) :
    (fieldTripleScalarAction K t).dualMap (fieldTripleTraceCovector K a) =
      fieldTripleTraceCovector K (t • a) :=
  dualMap_fieldTripleScalarAction_trace K t a

/-- The coordinate trace map, bundled as a linear map over the prime field. -/
def fieldTripleTraceDualMap :
    FieldTriple K →ₗ[F] Module.Dual F (FieldTriple K) where
  toFun := fieldTripleTraceCovector K
  map_add' := by
    intro a b
    apply LinearMap.ext
    intro x
    change
      Algebra.trace F K ((a.1 + b.1) * x.1) +
          Algebra.trace F K ((a.2.1 + b.2.1) * x.2.1) +
          Algebra.trace F K ((a.2.2 + b.2.2) * x.2.2) =
        (Algebra.trace F K (a.1 * x.1) +
            Algebra.trace F K (a.2.1 * x.2.1) +
            Algebra.trace F K (a.2.2 * x.2.2)) +
          (Algebra.trace F K (b.1 * x.1) +
            Algebra.trace F K (b.2.1 * x.2.1) +
            Algebra.trace F K (b.2.2 * x.2.2))
    rw [add_mul, map_add, add_mul, map_add, add_mul, map_add]
    abel_nf
  map_smul' := by
    intro r a
    apply LinearMap.ext
    intro x
    change
      Algebra.trace F K ((r • a.1) * x.1) +
          Algebra.trace F K ((r • a.2.1) * x.2.1) +
          Algebra.trace F K ((r • a.2.2) * x.2.2) =
        r • (Algebra.trace F K (a.1 * x.1) +
          Algebra.trace F K (a.2.1 * x.2.1) +
          Algebra.trace F K (a.2.2 * x.2.2))
    rw [show (r • a.1) * x.1 = r • (a.1 * x.1) by
      rw [Algebra.smul_def, Algebra.smul_def]
      ring,
      show (r • a.2.1) * x.2.1 = r • (a.2.1 * x.2.1) by
        rw [Algebra.smul_def, Algebra.smul_def]
        ring,
      show (r • a.2.2) * x.2.2 = r • (a.2.2 * x.2.2) by
        rw [Algebra.smul_def, Algebra.smul_def]
        ring]
    simp only [map_smul]
    simp
    ring

/-- Nondegeneracy makes the coordinate trace map injective. -/
theorem fieldTripleTraceDualMap_injective :
    Function.Injective (fieldTripleTraceDualMap K) := by
  intro a b hab
  have hzero : fieldTripleTraceDualMap K (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  change fieldTripleTraceCovector K (a - b) = 0 at hzero
  have hcoord := (fieldTripleTraceCovector_eq_zero_iff K (a - b)).mp hzero
  exact sub_eq_zero.mp hcoord

/-- The coordinatewise trace pairing identifies the field three-space with
its full binary dual, not just with a subspace of that dual. -/
noncomputable def fieldTripleTraceDualEquiv :
    FieldTriple K ≃ₗ[F] Module.Dual F (FieldTriple K) :=
  letI : Fact (Nat.Prime (ringChar K)) := ⟨CharP.prime_ringChar K⟩
  LinearMap.linearEquivOfInjective (fieldTripleTraceDualMap K)
    (fieldTripleTraceDualMap_injective K) (by simp)

/-- Scalar multiplication and its actual dual map are conjugate under the
trace-coordinate equivalence. -/
theorem fieldTripleScalarAction_dualMap_conjugate (t : K) :
    (fieldTripleScalarAction K t).dualMap.comp
        (fieldTripleTraceDualEquiv K).toLinearMap =
      (fieldTripleTraceDualEquiv K).toLinearMap.comp
        (fieldTripleScalarAction K t) := by
  apply LinearMap.ext
  intro a
  change
    (fieldTripleScalarAction K t).dualMap (fieldTripleTraceDualEquiv K a) =
      fieldTripleTraceDualEquiv K (fieldTripleScalarAction K t a)
  exact dualMap_fieldTripleScalarAction_trace K t a

/-- For every binary support subspace, the actual dual action on its
trace-coordinate image is exactly the image of the scalar translate. -/
theorem fieldTripleScalarAction_map_traceSupport
    (U : Submodule F (FieldTriple K)) (t : K) :
    Submodule.map (fieldTripleScalarAction K t).dualMap
        (Submodule.map (fieldTripleTraceDualEquiv K).toLinearMap U) =
      Submodule.map (fieldTripleTraceDualEquiv K).toLinearMap
        (Submodule.map (fieldTripleScalarAction K t) U) := by
  rw [← Submodule.map_comp,
    fieldTripleScalarAction_dualMap_conjugate K t,
    Submodule.map_comp]

end

end CorruptedFieldRecovery
