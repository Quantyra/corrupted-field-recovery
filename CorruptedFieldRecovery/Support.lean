import CorruptedFieldRecovery.BinaryTensor
import CorruptedFieldRecovery.Defect
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.LinearAlgebra.Projection

/-! Common-support semantics for the manuscript's actual binary alternating tensors.

The support is represented by the span of third-slot contractions.  Its orthogonal
subspace is the dual coannihilator supplied by mathlib.  The quotient theorem below
constructs an actual trilinear tensor on the quotient; it does not define factoring
to mean a mode-image bound.
-/

namespace CorruptedFieldRecovery

open Module LinearMap Submodule

variable {n : ℕ}

/-- Alternation for trilinear forms on an arbitrary binary vector space. -/
def IsAlternatingTrilinearOn {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (E : Trilinear (ZMod 2) V) : Prop :=
  (∀ x y, E x x y = 0) ∧ (∀ x y, E x y x = 0) ∧ (∀ x y, E x y y = 0)

/-- A mode-image bound is equivalent to vanishing on the annihilator of the proposed support. -/
theorem modeImage_le_iff_vanishes_on_dualCoannihilator
    (E : Trilinear (ZMod 2) (BinaryVector n))
    (U : Submodule (ZMod 2) (Module.Dual (ZMod 2) (BinaryVector n))) :
    modeImage E ≤ U ↔
      ∀ x y v, v ∈ U.dualCoannihilator → E x y v = 0 := by
  constructor
  · intro h x y v hv
    have hm : E x y ∈ modeImage E :=
      Submodule.subset_span ⟨(x, y), rfl⟩
    have hu : E x y ∈ U := h hm
    exact ((Submodule.mem_dualCoannihilator v).mp hv) (E x y) hu
  · intro h
    apply Submodule.span_le.mpr
    rintro φ ⟨⟨x, y⟩, rfl⟩
    haveI : FiniteDimensional (ZMod 2) (BinaryVector n) := inferInstance
    haveI : FiniteDimensional (ZMod 2)
        (Module.Dual (ZMod 2) (BinaryVector n)) := inferInstance
    have hdouble : U.dualCoannihilator.dualAnnihilator = U :=
      Subspace.dualCoannihilator_dualAnnihilator_eq (W := U)
    rw [← hdouble]
    change E x y ∈ U.dualCoannihilator.dualAnnihilator
    rw [Submodule.mem_dualAnnihilator]
    exact fun v hv => h x y v hv

/-- Alternation makes vanishing in the third slot imply vanishing in every slot over `F₂`. -/
theorem alternating_vanishes_on_dualCoannihilator_all_slots
    (E : BinaryTensor n)
    (hE : IsAlternating E)
    (U : Submodule (ZMod 2) (Module.Dual (ZMod 2) (BinaryVector n)))
    (h : ∀ x y v, v ∈ U.dualCoannihilator → E x y v = 0) :
    ∀ x y z, x ∈ U.dualCoannihilator ∨ y ∈ U.dualCoannihilator ∨
      z ∈ U.dualCoannihilator → E x y z = 0 := by
  intro x y z hxyz
  have hx' : E x y z = E z y x := (alternating_swap13 hE x y z).symm
  have hy' : E x y z = E x z y := alternating_swap23 hE x z y
  rcases hxyz with hx | hy | hz
  · calc
      E x y z = E z y x := hx'
      _ = 0 := h z y x hx
  · calc
      E x y z = E x z y := hy'
      _ = 0 := h x z y hy
  · exact h x y z hz

/-- Choose a linear complement and use its quotient equivalence to select representatives. -/
noncomputable def supportedQuotientSection
    (N : Submodule (ZMod 2) (BinaryVector n)) :
    (BinaryVector n ⧸ N) →ₗ[ZMod 2] BinaryVector n := by
  classical
  letI : FiniteDimensional (ZMod 2) (BinaryVector n) := inferInstance
  let P := Classical.choose (Submodule.exists_isCompl N)
  have hP : IsCompl N P := Classical.choose_spec (Submodule.exists_isCompl N)
  exact P.subtype.comp (N.quotientEquivOfIsCompl P hP).toLinearMap

theorem supportedQuotientSection_mkQ
    (N : Submodule (ZMod 2) (BinaryVector n))
    (q : BinaryVector n ⧸ N) : N.mkQ (supportedQuotientSection N q) = q := by
  classical
  letI : FiniteDimensional (ZMod 2) (BinaryVector n) := inferInstance
  let P := Classical.choose (Submodule.exists_isCompl N)
  have hP : IsCompl N P := Classical.choose_spec (Submodule.exists_isCompl N)
  change N.mkQ (P.subtype ((N.quotientEquivOfIsCompl P hP) q)) = q
  exact Submodule.mk_quotientEquivOfIsCompl_apply (p := N) (q := P) hP q

theorem supported_replace_first
    (E : Trilinear (ZMod 2) (BinaryVector n))
    (N : Submodule (ZMod 2) (BinaryVector n))
    (h₁ : ∀ x y z, x ∈ N → E x y z = 0)
    {x x' y z : BinaryVector n} (hx : x - x' ∈ N) : E x y z = E x' y z := by
  calc
    E x y z = E ((x - x') + x') y z := by rw [sub_add_cancel]
    _ = E (x - x') y z + E x' y z :=
      congrArg (fun f : BinaryVector n →ₗ[ZMod 2]
        BinaryVector n →ₗ[ZMod 2] ZMod 2 => f y z) (map_add E (x - x') x')
    _ = E x' y z := by rw [h₁ (x - x') y z hx, zero_add]

theorem supported_replace_second
    (E : Trilinear (ZMod 2) (BinaryVector n))
    (N : Submodule (ZMod 2) (BinaryVector n))
    (h₂ : ∀ x y z, y ∈ N → E x y z = 0)
    {x y y' z : BinaryVector n} (hy : y - y' ∈ N) : E x y z = E x y' z := by
  calc
    E x y z = E x ((y - y') + y') z := by rw [sub_add_cancel]
    _ = E x (y - y') z + E x y' z :=
      congrArg (fun f : BinaryVector n →ₗ[ZMod 2] ZMod 2 => f z)
        (map_add (E x) (y - y') y')
    _ = E x y' z := by rw [h₂ x (y - y') z hy, zero_add]

theorem supported_replace_third
    (E : Trilinear (ZMod 2) (BinaryVector n))
    (N : Submodule (ZMod 2) (BinaryVector n))
    (h₃ : ∀ x y z, z ∈ N → E x y z = 0)
    {x y z z' : BinaryVector n} (hz : z - z' ∈ N) : E x y z = E x y z' := by
  calc
    E x y z = E x y ((z - z') + z') := by rw [sub_add_cancel]
    _ = E x y (z - z') + E x y z' := map_add (E x y) (z - z') z'
    _ = E x y z' := by rw [h₃ x y (z - z') hz, zero_add]

noncomputable def supportedQuotientLift
    (E : Trilinear (ZMod 2) (BinaryVector n))
    (N : Submodule (ZMod 2) (BinaryVector n)) :
    Trilinear (ZMod 2) (BinaryVector n ⧸ N) :=
  pullback E (supportedQuotientSection N)

@[simp]
theorem supportedQuotientLift_mkQ
    (E : Trilinear (ZMod 2) (BinaryVector n))
    (N : Submodule (ZMod 2) (BinaryVector n))
    (h₁ : ∀ x y z, x ∈ N → E x y z = 0)
    (h₂ : ∀ x y z, y ∈ N → E x y z = 0)
    (h₃ : ∀ x y z, z ∈ N → E x y z = 0)
    (x y z : BinaryVector n) :
    supportedQuotientLift E N (N.mkQ x) (N.mkQ y) (N.mkQ z) = E x y z := by
  have hxq : N.mkQ (x - supportedQuotientSection N (N.mkQ x)) = 0 := by
    rw [map_sub, supportedQuotientSection_mkQ, sub_self]
  have hyq : N.mkQ (y - supportedQuotientSection N (N.mkQ y)) = 0 := by
    rw [map_sub, supportedQuotientSection_mkQ, sub_self]
  have hzq : N.mkQ (z - supportedQuotientSection N (N.mkQ z)) = 0 := by
    rw [map_sub, supportedQuotientSection_mkQ, sub_self]
  have hx : x - supportedQuotientSection N (N.mkQ x) ∈ N :=
    (Submodule.Quotient.mk_eq_zero N).1 hxq
  have hy : y - supportedQuotientSection N (N.mkQ y) ∈ N :=
    (Submodule.Quotient.mk_eq_zero N).1 hyq
  have hz : z - supportedQuotientSection N (N.mkQ z) ∈ N :=
    (Submodule.Quotient.mk_eq_zero N).1 hzq
  have hrep : E x y z = E (supportedQuotientSection N (N.mkQ x))
      (supportedQuotientSection N (N.mkQ y))
      (supportedQuotientSection N (N.mkQ z)) := calc
    E x y z = E (supportedQuotientSection N (N.mkQ x)) y z :=
      supported_replace_first E N h₁ hx
    _ = E (supportedQuotientSection N (N.mkQ x))
        (supportedQuotientSection N (N.mkQ y)) z :=
      supported_replace_second E N h₂ hy
    _ = E (supportedQuotientSection N (N.mkQ x))
        (supportedQuotientSection N (N.mkQ y))
        (supportedQuotientSection N (N.mkQ z)) :=
      supported_replace_third E N h₃ hz
  rw [supportedQuotientLift, pullback_apply]
  exact hrep.symm

/-- Every common-support bound yields a genuine factorization through `V/U⊥` in all slots. -/
theorem exists_supported_quotient_factorization
    (E : BinaryTensor n)
    (hE : IsAlternating E)
    (U : Submodule (ZMod 2) (Module.Dual (ZMod 2) (BinaryVector n)))
    (hU : modeImage E ≤ U) :
    ∃ e : Trilinear (ZMod 2) (BinaryVector n ⧸ U.dualCoannihilator),
      ∀ x y z, e (U.dualCoannihilator.mkQ x)
        (U.dualCoannihilator.mkQ y) (U.dualCoannihilator.mkQ z) = E x y z := by
  have hthird : ∀ x y z, z ∈ U.dualCoannihilator → E x y z = 0 :=
    (modeImage_le_iff_vanishes_on_dualCoannihilator E U).mp hU
  have hall := alternating_vanishes_on_dualCoannihilator_all_slots E hE U hthird
  refine ⟨supportedQuotientLift E U.dualCoannihilator, ?_⟩
  intro x y z
  exact supportedQuotientLift_mkQ E U.dualCoannihilator
    (fun x y z hx => hall x y z (Or.inl hx))
    (fun x y z hy => hall x y z (Or.inr (Or.inl hy)))
    (fun x y z hz => hall x y z (Or.inr (Or.inr hz))) x y z

/-- An alternating form remains alternating after factoring through a surjective quotient. -/
theorem alternating_of_supported_quotient_factorization
    (E : BinaryTensor n)
    (hE : IsAlternating E)
    (N : Submodule (ZMod 2) (BinaryVector n))
    (e : Trilinear (ZMod 2) (BinaryVector n ⧸ N))
    (hfac : ∀ x y z, e (N.mkQ x) (N.mkQ y) (N.mkQ z) = E x y z) :
    IsAlternatingTrilinearOn e := by
  constructor
  · intro x y
    obtain ⟨x', rfl⟩ := Submodule.mkQ_surjective N x
    obtain ⟨y', rfl⟩ := Submodule.mkQ_surjective N y
    rw [hfac x' x' y']
    exact hE.1 x' y'
  constructor
  · intro x y
    obtain ⟨x', rfl⟩ := Submodule.mkQ_surjective N x
    obtain ⟨y', rfl⟩ := Submodule.mkQ_surjective N y
    rw [hfac x' y' x']
    exact hE.2.1 x' y'
  · intro x y
    obtain ⟨x', rfl⟩ := Submodule.mkQ_surjective N x
    obtain ⟨y', rfl⟩ := Submodule.mkQ_surjective N y
    rw [hfac x' y' y']
    exact hE.2.2 x' y'

/-- The quotient factor returned for an alternating input is itself proved alternating. -/
theorem exists_alternating_supported_quotient_factorization
    (E : BinaryTensor n)
    (hE : IsAlternating E)
    (U : Submodule (ZMod 2) (Module.Dual (ZMod 2) (BinaryVector n)))
    (hU : modeImage E ≤ U) :
    ∃ e : Trilinear (ZMod 2) (BinaryVector n ⧸ U.dualCoannihilator),
      IsAlternatingTrilinearOn e ∧
        ∀ x y z, e (U.dualCoannihilator.mkQ x)
          (U.dualCoannihilator.mkQ y) (U.dualCoannihilator.mkQ z) = E x y z := by
  obtain ⟨e, hfac⟩ := exists_supported_quotient_factorization E hE U hU
  exact ⟨e, alternating_of_supported_quotient_factorization E hE _ e hfac, hfac⟩

/-- A quotient factorization forces every contraction into the proposed support. -/
theorem modeImage_le_of_supported_quotient_factorization
    (E : BinaryTensor n)
    (U : Submodule (ZMod 2) (Module.Dual (ZMod 2) (BinaryVector n)))
    (e : Trilinear (ZMod 2) (BinaryVector n ⧸ U.dualCoannihilator))
    (hfac : ∀ x y z, e (U.dualCoannihilator.mkQ x)
      (U.dualCoannihilator.mkQ y) (U.dualCoannihilator.mkQ z) = E x y z) :
    modeImage E ≤ U := by
  apply (modeImage_le_iff_vanishes_on_dualCoannihilator E U).mpr
  intro x y v hv
  rw [← hfac]
  have hvq : U.dualCoannihilator.mkQ v = 0 :=
    (Submodule.Quotient.mk_eq_zero U.dualCoannihilator).2 hv
  rw [hvq]
  simp

/-- For alternating binary tensors, common support and actual quotient factorization coincide. -/
theorem modeImage_le_iff_exists_supported_quotient_factorization
    (E : BinaryTensor n)
    (hE : IsAlternating E)
    (U : Submodule (ZMod 2) (Module.Dual (ZMod 2) (BinaryVector n))) :
    modeImage E ≤ U ↔
      ∃ e : Trilinear (ZMod 2) (BinaryVector n ⧸ U.dualCoannihilator),
        IsAlternatingTrilinearOn e ∧
          ∀ x y z, e (U.dualCoannihilator.mkQ x)
            (U.dualCoannihilator.mkQ y) (U.dualCoannihilator.mkQ z) = E x y z := by
  constructor
  · exact exists_alternating_supported_quotient_factorization E hE U
  · rintro ⟨e, _, hfac⟩
    exact modeImage_le_of_supported_quotient_factorization E U e hfac

/-- The actual mode image is a common support and is contained in every common support. -/
theorem modeImage_is_minimal_common_support
    (E : BinaryTensor n)
    (hE : IsAlternating E) :
    (∃ e : Trilinear
        (ZMod 2) (BinaryVector n ⧸ (modeImage E).dualCoannihilator),
      IsAlternatingTrilinearOn e ∧
        ∀ x y z, e ((modeImage E).dualCoannihilator.mkQ x)
          ((modeImage E).dualCoannihilator.mkQ y)
          ((modeImage E).dualCoannihilator.mkQ z) = E x y z) ∧
      (∀ U : Submodule (ZMod 2) (Module.Dual (ZMod 2) (BinaryVector n)),
        ∀ e : Trilinear (ZMod 2) (BinaryVector n ⧸ U.dualCoannihilator),
          (∀ x y z, e (U.dualCoannihilator.mkQ x)
            (U.dualCoannihilator.mkQ y) (U.dualCoannihilator.mkQ z) = E x y z) →
          modeImage E ≤ U) := by
  constructor
  · exact exists_alternating_supported_quotient_factorization E hE (modeImage E) le_rfl
  · intro U e hfac
    exact modeImage_le_of_supported_quotient_factorization E U e hfac

end CorruptedFieldRecovery
