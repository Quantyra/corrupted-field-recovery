import CorruptedFieldRecovery.BinaryTensor
import CorruptedFieldRecovery.Defect
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Quotient.Bilinear

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

/- The inner two slots of a trilinear form lifted through a quotient. -/
theorem supportedSecondKernel
    (E : Trilinear (ZMod 2) (BinaryVector n))
    (N : Submodule (ZMod 2) (BinaryVector n))
    (h₂ : ∀ x y z, y ∈ N → E x y z = 0)
    (x : BinaryVector n) : N ≤ LinearMap.ker (E x) := by
  intro y hy
  apply LinearMap.ext
  intro z
  exact h₂ x y z hy

theorem supportedThirdKernel
    (E : Trilinear (ZMod 2) (BinaryVector n))
    (N : Submodule (ZMod 2) (BinaryVector n))
    (h₃ : ∀ x y z, z ∈ N → E x y z = 0)
    (x : BinaryVector n) : N ≤ LinearMap.ker (E x).flip := by
  intro z hz
  apply LinearMap.ext
  intro y
  exact h₃ x y z hz

noncomputable def supportedInnerLift
    (E : Trilinear (ZMod 2) (BinaryVector n))
    (N : Submodule (ZMod 2) (BinaryVector n))
    (h₂ : ∀ x y z, y ∈ N → E x y z = 0)
    (h₃ : ∀ x y z, z ∈ N → E x y z = 0) :
    BinaryVector n →ₗ[ZMod 2]
      (BinaryVector n ⧸ N →ₗ[ZMod 2] BinaryVector n ⧸ N →ₗ[ZMod 2] ZMod 2) := by
  let hsecond := fun x => supportedSecondKernel E N h₂ x
  let hthird := fun x => supportedThirdKernel E N h₃ x
  have liftEval (x y z : BinaryVector n) :
      (E x).liftQ₂ N N (hsecond x) (hthird x) (N.mkQ y) (N.mkQ z) = E x y z := by
    exact LinearMap.liftQ₂_mk (hsecond x) (hthird x) y z
  exact {
    toFun := fun x => (E x).liftQ₂ N N (hsecond x) (hthird x)
    map_add' := by
      intro x y
      apply LinearMap.ext
      intro q
      apply LinearMap.ext
      intro r
      obtain ⟨q', rfl⟩ := Submodule.mkQ_surjective N q
      obtain ⟨r', rfl⟩ := Submodule.mkQ_surjective N r
      change (E (x + y)).liftQ₂ N N (hsecond (x + y)) (hthird (x + y))
          (N.mkQ q') (N.mkQ r') =
        (E x).liftQ₂ N N (hsecond x) (hthird x) (N.mkQ q') (N.mkQ r') +
        (E y).liftQ₂ N N (hsecond y) (hthird y) (N.mkQ q') (N.mkQ r')
      rw [liftEval, liftEval, liftEval]
      exact congrArg (fun f : BinaryVector n →ₗ[ZMod 2]
        BinaryVector n →ₗ[ZMod 2] ZMod 2 => f q' r') (map_add E x y)
    map_smul' := by
      intro a x
      apply LinearMap.ext
      intro q
      apply LinearMap.ext
      intro r
      obtain ⟨q', rfl⟩ := Submodule.mkQ_surjective N q
      obtain ⟨r', rfl⟩ := Submodule.mkQ_surjective N r
      change (E (a • x)).liftQ₂ N N (hsecond (a • x)) (hthird (a • x))
          (N.mkQ q') (N.mkQ r') =
        a • ((E x).liftQ₂ N N (hsecond x) (hthird x) (N.mkQ q') (N.mkQ r'))
      rw [liftEval, liftEval]
      exact congrArg (fun f : BinaryVector n →ₗ[ZMod 2]
        BinaryVector n →ₗ[ZMod 2] ZMod 2 => f q' r') (map_smul E a x) }

@[simp]
theorem supportedInnerLift_mkQ
    (E : Trilinear (ZMod 2) (BinaryVector n))
    (N : Submodule (ZMod 2) (BinaryVector n))
    (h₂ : ∀ x y z, y ∈ N → E x y z = 0)
    (h₃ : ∀ x y z, z ∈ N → E x y z = 0)
    (x y z : BinaryVector n) :
    supportedInnerLift E N h₂ h₃ x (N.mkQ y) (N.mkQ z) = E x y z := by
  change (E x).liftQ₂ N N
      (supportedSecondKernel E N h₂ x) (supportedThirdKernel E N h₃ x)
      (N.mkQ y) (N.mkQ z) = E x y z
  exact LinearMap.liftQ₂_mk
    (supportedSecondKernel E N h₂ x) (supportedThirdKernel E N h₃ x) y z

theorem supportedInnerLift_firstKernel
    (E : Trilinear (ZMod 2) (BinaryVector n))
    (N : Submodule (ZMod 2) (BinaryVector n))
    (h₁ : ∀ x y z, x ∈ N → E x y z = 0)
    (h₂ : ∀ x y z, y ∈ N → E x y z = 0)
    (h₃ : ∀ x y z, z ∈ N → E x y z = 0) :
    N ≤ LinearMap.ker (supportedInnerLift E N h₂ h₃) := by
  intro x hx
  apply LinearMap.ext
  intro q
  apply LinearMap.ext
  intro r
  obtain ⟨q', rfl⟩ := Submodule.mkQ_surjective N q
  obtain ⟨r', rfl⟩ := Submodule.mkQ_surjective N r
  change supportedInnerLift E N h₂ h₃ x (N.mkQ q') (N.mkQ r') = 0
  rw [supportedInnerLift_mkQ]
  exact h₁ x q' r' hx

/- Lift the first slot, after `supportedInnerLift` has lifted the other two. -/
noncomputable def supportedQuotientLift
    (E : Trilinear (ZMod 2) (BinaryVector n))
    (N : Submodule (ZMod 2) (BinaryVector n))
    (h₁ : ∀ x y z, x ∈ N → E x y z = 0)
    (h₂ : ∀ x y z, y ∈ N → E x y z = 0)
    (h₃ : ∀ x y z, z ∈ N → E x y z = 0) :
    (BinaryVector n ⧸ N) →ₗ[ZMod 2]
      BinaryVector n ⧸ N →ₗ[ZMod 2] BinaryVector n ⧸ N →ₗ[ZMod 2] ZMod 2 := by
  let G : BinaryVector n →ₗ[ZMod 2]
      (BinaryVector n ⧸ N →ₗ[ZMod 2] BinaryVector n ⧸ N →ₗ[ZMod 2] ZMod 2) :=
    supportedInnerLift E N h₂ h₃
  exact N.liftQ G (supportedInnerLift_firstKernel E N h₁ h₂ h₃)

@[simp]
theorem supportedQuotientLift_mkQ
    (E : Trilinear (ZMod 2) (BinaryVector n))
    (N : Submodule (ZMod 2) (BinaryVector n))
    (h₁ : ∀ x y z, x ∈ N → E x y z = 0)
    (h₂ : ∀ x y z, y ∈ N → E x y z = 0)
    (h₃ : ∀ x y z, z ∈ N → E x y z = 0)
    (x y z : BinaryVector n) :
    supportedQuotientLift E N h₁ h₂ h₃ (N.mkQ x) (N.mkQ y) (N.mkQ z) = E x y z := by
  rw [supportedQuotientLift, Submodule.liftQ_apply, supportedInnerLift_mkQ]

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
  refine ⟨supportedQuotientLift E U.dualCoannihilator
      (fun x y z hx => hall x y z (Or.inl hx))
      (fun x y z hy => hall x y z (Or.inr (Or.inl hy)))
      (fun x y z hz => hall x y z (Or.inr (Or.inr hz))), ?_⟩
  intro x y z
  exact supportedQuotientLift_mkQ E _ _ _ _ x y z

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
