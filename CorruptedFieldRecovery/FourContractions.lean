import Mathlib.FieldTheory.Finite.Trace
import Mathlib.Algebra.CharP.Two

/-! Algebraic core for the four-contraction field-identification route.

This file deliberately does not claim M2a coverage: the concrete determinant
contractions, their trace radicals, block extraction, and arbitrary sampled-basis
transport still have to be connected to the algebraic core below.
-/

namespace CorruptedFieldRecovery

/-- The finite-field trace pairing is nondegenerate in either argument. -/
theorem tracePairing_nondegenerate
    (K : Type*) [Field K] [Finite K] [Algebra (ZMod (ringChar K)) K]
    (λ : K) (hλ : λ ≠ 0) (x : K) (hx : x ≠ 0) :
    ∃ y : K, Algebra.trace (ZMod (ringChar K)) K (λ * x * y) ≠ 0 := by
  obtain ⟨y, hy⟩ := FiniteField.trace_to_zmod_nondegenerate K (mul_ne_zero hλ hx)
  exact ⟨y, by simpa [mul_assoc] using hy⟩

/-- An F-linear map on a finite field that commutes with multiplication by an
algebra generator is multiplication by its value at one. This is the scalar
recognition step used after the first three contractions identify one common
self-adjoint block map. -/
theorem linearMap_scalar_of_commutes_generator
    (F K : Type*) [CommSemiring F] [Field K] [Algebra F K]
    (A : K →ₗ[F] K) (α : K)
    (hgen : Algebra.adjoin F {α} = ⊤)
    (hcomm : ∀ x : K, A (α * x) = α * A x) :
    ∀ x : K, A x = A 1 * x := by
  have hmul : ∀ r : K, r ∈ Algebra.adjoin F {α} → ∀ x : K,
      A (r * x) = r * A x := by
    intro r hr
    rw [Algebra.mem_adjoin_iff] at hr
    induction hr using Subring.closure_induction with
    | mem r hr =>
        rcases hr with ⟨t, rfl⟩ | hr
        · intro x
          rw [Algebra.smul_def, map_smul]
          simp [Algebra.smul_def]
        · have hr : r = α := by simpa using hr
          subst r
          exact hcomm
    | zero =>
        intro x
        simp
    | one =>
        intro x
        simp
    | add r s hr hs ihr ihs =>
        intro x
        rw [add_mul, map_add, ihr x, ihs x, add_mul]
    | neg r hr ihr =>
        intro x
        rw [neg_mul, map_neg, ihr x, neg_mul]
    | mul r s hr hs ihr ihs =>
        intro x
        rw [mul_assoc, ihr (s * x), ihs x, mul_assoc]
  have htop : ∀ r : K, ∀ x : K, A (r * x) = r * A x := by
    intro r x
    apply hmul r
    rw [hgen]
    trivial
  intro x
  simpa [mul_comm] using (htop x 1)

end CorruptedFieldRecovery
