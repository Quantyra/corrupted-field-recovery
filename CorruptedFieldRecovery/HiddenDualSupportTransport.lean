import CorruptedFieldRecovery.BinaryFieldTransport
import CorruptedFieldRecovery.Bridge
import CorruptedFieldRecovery.TraceDualTranslateBridge

/-! Transport of the fifth-scalar action and binary support from hidden
physical coordinates to the actual physical dual. The hidden isomorphism is
kept as an explicit hypothesis. -/

namespace CorruptedFieldRecovery

noncomputable section

variable (K : Type*) [Field K] [Finite K]
variable [Algebra (ZMod (ringChar K)) K]

local notation "F" => ZMod (ringChar K)

/-- The physical dual is identified with field coordinates by the coordinate
trace equivalence followed by the dual map of the hidden input isomorphism. -/
noncomputable def hiddenTraceDualEquiv {n : Nat}
    (ι : BinaryInput K n ≃ₗ[F] FieldTriple K) :
    FieldTriple K ≃ₗ[F] Module.Dual F (BinaryInput K n) := by
  letI : Fact (Nat.Prime (ringChar K)) := ⟨CharP.prime_ringChar K⟩
  exact (fieldTripleTraceDualEquiv K).trans ι.dualMap

/-- If the physical endomorphism is scalar multiplication after the hidden
coordinate isomorphism, its actual dual map is the same scalar action under
the trace-coordinate identification. -/
theorem hiddenTraceDualEquiv_dualAction {n : Nat}
    (ι : BinaryInput K n ≃ₗ[F] FieldTriple K)
    (T : Module.End F (BinaryInput K n)) (t : K)
    (hT : ∀ x, ι (T x) = fieldTripleScalarAction K t (ι x))
    (a : FieldTriple K) :
    T.dualMap (hiddenTraceDualEquiv K ι a) =
      hiddenTraceDualEquiv K ι (t • a) := by
  letI : Fact (Nat.Prime (ringChar K)) := ⟨CharP.prime_ringChar K⟩
  apply LinearMap.ext
  intro x
  change fieldTripleTraceCovector K a (ι (T x)) =
    fieldTripleTraceCovector K (t • a) (ι x)
  rw [hT x]
  have hp := congrArg
    (fun f : Module.Dual F (FieldTriple K) => f (ι x))
    (dualMap_fieldTripleScalarAction_trace K t a)
  simpa only [LinearMap.dualMap_apply] using hp

/-- Conjugation identity for the physical dual map and the scalar action on
field coordinates. -/
theorem hiddenTraceDualEquiv_dualMap_conjugate {n : Nat}
    (ι : BinaryInput K n ≃ₗ[F] FieldTriple K)
    (T : Module.End F (BinaryInput K n)) (t : K)
    (hT : ∀ x, ι (T x) = fieldTripleScalarAction K t (ι x)) :
    T.dualMap.comp (hiddenTraceDualEquiv K ι).toLinearMap =
      (hiddenTraceDualEquiv K ι).toLinearMap.comp (fieldTripleScalarAction K t) := by
  apply LinearMap.ext
  intro a
  exact hiddenTraceDualEquiv_dualAction K ι T t hT a

/-- Action on a binary support subspace commutes with transporting that
subspace to the physical dual. -/
theorem hiddenTraceDualEquiv_map_support {n : Nat}
    (ι : BinaryInput K n ≃ₗ[F] FieldTriple K)
    (T : Module.End F (BinaryInput K n)) (t : K)
    (hT : ∀ x, ι (T x) = fieldTripleScalarAction K t (ι x))
    (U : Submodule F (FieldTriple K)) :
    Submodule.map T.dualMap
        (Submodule.map (hiddenTraceDualEquiv K ι).toLinearMap U) =
      Submodule.map (hiddenTraceDualEquiv K ι).toLinearMap
        (Submodule.map (fieldTripleScalarAction K t) U) := by
  rw [← Submodule.map_comp,
    hiddenTraceDualEquiv_dualMap_conjugate K ι T t hT,
    Submodule.map_comp]

/-- The trace-coordinate equivalence preserves exactly the disjointness
condition used by the manuscript's two-translate bridge. -/
theorem hiddenTraceDualEquiv_disjoint_iff {n : Nat}
    (ι : BinaryInput K n ≃ₗ[F] FieldTriple K)
    (U V : Submodule F (FieldTriple K)) :
    Disjoint
        (Submodule.map (hiddenTraceDualEquiv K ι).toLinearMap U)
        (Submodule.map (hiddenTraceDualEquiv K ι).toLinearMap V) ↔
      Disjoint U V := by
  letI : Fact (Nat.Prime (ringChar K)) := ⟨CharP.prime_ringChar K⟩
  constructor
  · intro h
    have h' := Submodule.disjoint_map
      (hiddenTraceDualEquiv K ι).symm.injective h
    have hU : Submodule.map (hiddenTraceDualEquiv K ι).symm.toLinearMap
        (Submodule.map (hiddenTraceDualEquiv K ι).toLinearMap U) = U := by
      rw [← Submodule.map_comp]
      simp
    have hV : Submodule.map (hiddenTraceDualEquiv K ι).symm.toLinearMap
        (Submodule.map (hiddenTraceDualEquiv K ι).toLinearMap V) = V := by
      rw [← Submodule.map_comp]
      simp
    rw [hU, hV] at h'
    exact h'
  · intro h
    exact Submodule.disjoint_map
      (hiddenTraceDualEquiv K ι).injective h

/-- The actual four-balance theorem supplies the scalar needed for the
physical dual support/action transport. Its coefficient and generator
hypotheses remain explicit. -/
theorem hiddenFourBalanced_dualSupport_action
    [Fintype K] [CharP K 2]
    {n : Nat} (ι : BinaryInput K n ≃ₗ[F] FieldTriple K)
    (basis : Module.Basis (Fin 3) K (FieldTriple K)) (v : FieldTriple K)
    (c : K) (hc : c ≠ 0)
    (hgen : Algebra.adjoin F {(sampledBasisCoordinateEquiv K basis v).1} = ⊤ ∨
      Algebra.adjoin F {(sampledBasisCoordinateEquiv K basis v).2.1} = ⊤ ∨
      Algebra.adjoin F {(sampledBasisCoordinateEquiv K basis v).2.2} = ⊤)
    (T : Module.End F (BinaryInput K n))
    (hbal : hiddenFourBalanced K ι basis v c T)
    (U : Submodule F (FieldTriple K)) :
    ∃ t : K,
      Submodule.map T.dualMap
          (Submodule.map (hiddenTraceDualEquiv K ι).toLinearMap U) =
        Submodule.map (hiddenTraceDualEquiv K ι).toLinearMap
          (Submodule.map (fieldTripleScalarAction K t) U) := by
  have hclass :=
    (hidden_four_contractions_identification K ι basis v c hc hgen).1 T
  obtain ⟨t, hT⟩ := hclass.mp hbal
  refine ⟨t, ?_⟩
  apply hiddenTraceDualEquiv_map_support K ι T t ?_ U
  intro x
  have hx := congrArg ι (hT x)
  simpa [fieldTripleScalarAction] using hx

end

end CorruptedFieldRecovery
