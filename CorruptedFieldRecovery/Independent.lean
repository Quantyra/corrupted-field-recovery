import CorruptedFieldRecovery.Defect
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Prod

/-! The linear-algebra bridge from disjoint translated covector spaces to
the joint-surjectivity condition in the defect-image theorem. -/

namespace CorruptedFieldRecovery

variable {F V W : Type*} [Field F]
variable [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

theorem joint_surjective_of_disjoint_duals (u v : V →ₗ[F] W)
    (hu : Function.Surjective u) (hv : Function.Surjective v)
    (hd : Disjoint (LinearMap.range u.dualMap) (LinearMap.range v.dualMap)) :
    Function.Surjective (u.prod v) := by
  apply LinearMap.dualMap_injective_iff.mp
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro φ hφ
  let f : W →ₗ[F] F := φ.comp (LinearMap.inl F W W)
  let g : W →ₗ[F] F := φ.comp (LinearMap.inr F W W)
  have splitφ (x y : W) : φ (x, y) = f x + g y := by
    change φ (x, y) = φ (x, 0) + φ (0, y)
    rw [← map_add]
    simp
  have cancel : u.dualMap f = -(v.dualMap g) := by
    ext x
    have h0 := LinearMap.congr_fun hφ x
    change φ (u x, v x) = 0 at h0
    rw [splitφ] at h0
    exact eq_neg_of_add_eq_zero_left h0
  have hz : u.dualMap f = 0 := by
    apply (Submodule.disjoint_def.mp hd) (u.dualMap f)
    · exact ⟨f, rfl⟩
    · rw [cancel]
      exact Submodule.neg_mem _ ⟨g, rfl⟩
  have hf : f = 0 := LinearMap.dualMap_injective_of_surjective hu (by simpa using hz)
  have hg0 : v.dualMap g = 0 := by
    rw [hf, map_zero] at cancel
    exact neg_eq_zero.mp cancel.symm
  have hg : g = 0 := LinearMap.dualMap_injective_of_surjective hv (by simpa using hg0)
  apply LinearMap.ext
  intro xy
  rcases xy with ⟨x, y⟩
  change φ (x, y) = 0
  rw [splitφ]
  simp [hf, hg]

/-- The manuscript's two-translate lemma for an invertible action. The
support covector space is the range of the pullback u.dualMap. -/
theorem two_translate_of_disjoint (E : Trilinear F W) (u : V →ₗ[F] W)
    (T : V ≃ₗ[F] V) (hu : Function.Surjective u)
    (hd : Disjoint (LinearMap.range u.dualMap)
      (LinearMap.range (u.comp T.toLinearMap).dualMap)) :
    modeImage (imbalance (pullback E u) T.toLinearMap) = modeImage (pullback E u) := by
  apply two_translate_modeImage
  exact joint_surjective_of_disjoint_duals u (u.comp T.toLinearMap) hu
    (hu.comp T.surjective) hd

end CorruptedFieldRecovery
