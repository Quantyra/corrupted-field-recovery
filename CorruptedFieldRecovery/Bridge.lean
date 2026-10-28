import CorruptedFieldRecovery.Independent
import CorruptedFieldRecovery.BinaryTensor
import Mathlib.Algebra.CharP.Two

/-! The general restricted-dual bridge from the manuscript's two-translate
hypotheses to the abstract defect-image recovery theorem. -/

namespace CorruptedFieldRecovery

variable {F V W : Type*} [Field F]
variable [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

/-- Restricted injectivity on the support covectors and disjoint translated
images make the two observations jointly surjective. -/
theorem two_translate_of_restricted_injective_disjoint
    (E : Trilinear F W) (u : V →ₗ[F] W) (T : V →ₗ[F] V)
    (hu : Function.Surjective u)
    (hinj : Set.InjOn T.dualMap (LinearMap.range u.dualMap))
    (hd : Disjoint (LinearMap.range u.dualMap)
      (LinearMap.range (u.comp T).dualMap)) :
    modeImage (imbalance (pullback E u) T) = modeImage (pullback E u) := by
  have hu_dual : Function.Injective u.dualMap :=
    LinearMap.dualMap_injective_of_surjective hu
  have hcomp : Function.Injective ((T.dualMap).comp u.dualMap) := by
    intro f g hfg
    apply hu_dual
    apply hinj
    · exact ⟨f, rfl⟩
    · exact ⟨g, rfl⟩
    · exact hfg
  have hdual : Function.Injective (u.comp T).dualMap := by
    rw [← LinearMap.dualMap_comp_dualMap T u]
    exact hcomp
  have hsurj : Function.Surjective (u.comp T) :=
    LinearMap.dualMap_injective_iff.mp hdual
  exact two_translate_modeImage E u T
    (joint_surjective_of_disjoint_duals u (u.comp T) hu hsurj hd)

/-- Balanced compatible components cancel before applying the restricted-dual
bridge to the supported corruption. -/
theorem recovery_modeImage_of_restricted_injective_disjoint
    (C : Trilinear F V) (E : Trilinear F W)
    (u : V →ₗ[F] W) (T : V →ₗ[F] V)
    (balanced : ∀ x y z, C (T x) y z = C x (T y) z)
    (hu : Function.Surjective u)
    (hinj : Set.InjOn T.dualMap (LinearMap.range u.dualMap))
    (hd : Disjoint (LinearMap.range u.dualMap)
      (LinearMap.range (u.comp T).dualMap)) :
    modeImage (imbalance (C + pullback E u) T) = modeImage (pullback E u) := by
  rw [balanced_cancels C (pullback E u) T balanced]
  exact two_translate_of_restricted_injective_disjoint E u T hu hinj hd

/-- In characteristic two, the existing difference displacement is exactly
the manuscript's addition displacement. -/
theorem imbalance_apply_eq_add_of_char_two
    {n : ℕ} (E : BinaryTensor n) (T : BinaryVector n →ₗ[ZMod 2] BinaryVector n)
    (x y z : BinaryVector n) :
    imbalance E T x y z = E (T x) y z + E x (T y) z := by
  rw [imbalance_apply, CharTwo.sub_eq_add]

/-- Displacing an alternating binary tensor is symmetric in its first two
arguments, even though the displacement need not be fully alternating. -/
theorem imbalance_symmetric12_of_alternating
    {n : ℕ} (E : BinaryTensor n) (T : BinaryVector n →ₗ[ZMod 2] BinaryVector n)
    (hE : IsAlternating E) (x y z : BinaryVector n) :
    imbalance E T x y z = imbalance E T y x z := by
  rw [imbalance_apply_eq_add_of_char_two, imbalance_apply_eq_add_of_char_two]
  calc
    E (T x) y z + E x (T y) z =
        E y (T x) z + E (T y) x z := by
          rw [← alternating_swap12 hE (T x) y z,
            alternating_swap12 hE (T y) x z]
    _ = E (T y) x z + E y (T x) z := by abel

/-- The displaced alternating binary tensor vanishes when its first two
arguments agree. -/
theorem imbalance_zero_diagonal12_of_alternating
    {n : ℕ} (E : BinaryTensor n) (T : BinaryVector n →ₗ[ZMod 2] BinaryVector n)
    (hE : IsAlternating E) (x z : BinaryVector n) :
    imbalance E T x x z = 0 := by
  rw [imbalance_apply_eq_add_of_char_two, alternating_swap12 hE (T x) x z]
  exact CharTwo.add_self_eq_zero _

end CorruptedFieldRecovery