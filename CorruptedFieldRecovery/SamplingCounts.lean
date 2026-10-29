import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! Finite counting for the actual clean F₂-subspace used by recovery.

The intended instantiation is `V = K × K × K`, viewed as an F₂-space through
the manuscript's hidden linear isomorphism, and `u` is the promised support
map. Nothing here assumes that `ker u` is K-linear.
-/

namespace CorruptedFieldRecovery

open Module LinearMap

/- The kernel of a surjective support map of codimension `r` has the expected
number of physical binary vectors. `V` may be the hidden-coordinate copy of
`K³`; the only input about its dimension is stated explicitly. -/
theorem card_ker_support_f2
    {V W : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    [Fintype V] [Fintype W]
    (u : V →ₗ[ZMod 2] W) (hu : Function.Surjective u)
    (n r : ℕ) (hV : finrank (ZMod 2) V = n)
    (hW : finrank (ZMod 2) W = r) :
    Nat.card (LinearMap.ker u) = 2 ^ (n - r) := by
  classical
  have hrange : LinearMap.range u = ⊤ := LinearMap.range_eq_top.mpr hu
  have hdim := u.finrank_range_add_finrank_ker
  rw [hrange, finrank_top, hW, hV] at hdim
  have hrle : r ≤ n := by omega
  have hker : finrank (ZMod 2) (LinearMap.ker u) = n - r := by omega
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := LinearMap.ker u), hker, Nat.card_zmod]

/- Four independent uniform physical words are clean exactly when each lies
in the support kernel. This counts the finite sample space directly instead
of postulating a cleanliness probability. -/
theorem card_four_clean_words
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : Finset V) :
    Fintype.card {x : Fin 4 → V // ∀ i, x i ∈ A} = (A.card : ℕ) ^ 4 := by
  let e : {x : Fin 4 → V // ∀ i, x i ∈ A} ≃ (Fin 4 → {v // v ∈ A}) := {
    toFun := fun x i => ⟨x.1 i, x.2 i⟩
    invFun := fun x => ⟨fun i => (x i).1, fun i => (x i).2⟩
    left_inv := by intro x; apply Subtype.ext; rfl
    right_inv := by intro x; funext i; apply Subtype.ext; rfl
  }
  calc
    Fintype.card {x : Fin 4 → V // ∀ i, x i ∈ A} =
        Fintype.card (Fin 4 → {v // v ∈ A}) := Fintype.card_congr e
    _ = (Fintype.card {v // v ∈ A} : ℕ) ^ 4 := by simp
    _ = (A.card : ℕ) ^ 4 := by rw [Fintype.card_coe]

end CorruptedFieldRecovery
