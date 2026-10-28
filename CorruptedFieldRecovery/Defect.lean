import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Abel

/-! Algebraic defect-image recovery. The explicit split-surjectivity hypothesis
below is the coordinate consequence of independent covectors U and T*U.
The derivation of that hypothesis from the manuscript promise is a separate,
currently unformalized obligation. These exports are not the full theorem. -/

namespace CorruptedFieldRecovery

variable {F V W : Type*} [Field F]
variable [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

abbrev Trilinear (F V : Type*) [Field F] [AddCommGroup V] [Module F V] :=
  V →ₗ[F] V →ₗ[F] V →ₗ[F] F

/-- All covectors obtained by contracting the first two arguments. -/
def modeImage (E : Trilinear F V) : Submodule F (V →ₗ[F] F) :=
  Submodule.span F (Set.range fun xy : V × V => E xy.1 xy.2)

/-- Pull back a trilinear tensor along a linear observation map. -/
def pullback (E : Trilinear F W) (u : V →ₗ[F] W) : Trilinear F V :=
  { toFun := fun x =>
      { toFun := fun y => (E (u x) (u y)).comp u
        map_add' := by intros; ext; simp
        map_smul' := by intros; ext; simp }
    map_add' := by intros; ext; simp
    map_smul' := by intros; ext; simp }

@[simp] theorem pullback_apply (E : Trilinear F W) (u : V →ₗ[F] W)
    (x y z : V) : pullback E u x y z = E (u x) (u y) (u z) := rfl

/-- A difference, equal to a sum over the binary field. -/
def imbalance (E : Trilinear F V) (T : V →ₗ[F] V) : Trilinear F V :=
  { toFun := fun x =>
      { toFun := fun y => E (T x) y - E x (T y)
        map_add' := by intros; ext; simp; abel
        map_smul' := by intros; ext; simp [mul_sub] }
    map_add' := by intros; ext; simp; abel
    map_smul' := by intros; ext; simp [mul_sub] }

@[simp] theorem imbalance_apply (E : Trilinear F V) (T : V →ₗ[F] V)
    (x y z : V) : imbalance E T x y z = E (T x) y z - E x (T y) z := rfl

theorem imbalance_add (C E : Trilinear F V) (T : V →ₗ[F] V) :
    imbalance (C + E) T = imbalance C T + imbalance E T := by
  ext x y z
  simp only [imbalance_apply, LinearMap.add_apply]
  abel

/-- Balanced compatible tensors disappear under the difference operator. -/
theorem balanced_cancels (C E : Trilinear F V) (T : V →ₗ[F] V)
    (balanced : ∀ x y z, C (T x) y z = C x (T y) z) :
    imbalance (C + E) T = imbalance E T := by
  rw [imbalance_add]
  have h : imbalance C T = 0 := by
    ext x y z
    simp [balanced]
  rw [h, zero_add]

theorem imbalance_mode_le (E : Trilinear F V) (T : V →ₗ[F] V) :
    modeImage (imbalance E T) ≤ modeImage E := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨x, y⟩, rfl⟩
  change E (T x) y - E x (T y) ∈ modeImage E
  exact Submodule.sub_mem _
    (Submodule.subset_span ⟨(T x, y), rfl⟩)
    (Submodule.subset_span ⟨(x, T y), rfl⟩)

/-- If (u,uT) is onto, every original contracted covector can be isolated. -/
theorem two_translate_modeImage (E : Trilinear F W)
    (u : V →ₗ[F] W) (T : V →ₗ[F] V)
    (split : Function.Surjective fun x : V => (u x, u (T x))) :
    modeImage (imbalance (pullback E u) T) = modeImage (pullback E u) := by
  apply le_antisymm (imbalance_mode_le _ _)
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨x, y⟩, rfl⟩
  obtain ⟨a, ha⟩ := split (0, u x)
  have ha0 : u a = 0 := congrArg Prod.fst ha
  have ha1 : u (T a) = u x := congrArg Prod.snd ha
  have isolate : imbalance (pullback E u) T a y = pullback E u x y := by
    ext z
    simp [ha0, ha1]
  change pullback E u x y ∈ modeImage (imbalance (pullback E u) T)
  rw [← isolate]
  exact Submodule.subset_span ⟨(a, y), rfl⟩

theorem recovery_modeImage (C : Trilinear F V) (E : Trilinear F W)
    (u : V →ₗ[F] W) (T : V →ₗ[F] V)
    (balanced : ∀ x y z, C (T x) y z = C x (T y) z)
    (split : Function.Surjective fun x : V => (u x, u (T x))) :
    modeImage (imbalance (C + pullback E u) T) = modeImage (pullback E u) := by
  rw [balanced_cancels C (pullback E u) T balanced]
  exact two_translate_modeImage E u T split

end CorruptedFieldRecovery
