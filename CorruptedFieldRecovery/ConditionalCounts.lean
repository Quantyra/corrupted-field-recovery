import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic

/-! Finite conditional sampling bounds that do not assume the clean binary
subspace is linear over the hidden field. -/

namespace CorruptedFieldRecovery

noncomputable section

variable (K : Type*) [Fintype K] [DecidableEq K]

/-- A first-coordinate fiber in the ambient three-dimensional hidden-field
space has exactly `|K|^2` elements. -/
theorem card_first_coordinate_fiber (a : K) :
    Fintype.card {x : Fin 3 → K // x 0 = a} = Fintype.card K ^ 2 := by
  classical
  let e : {x : Fin 3 → K // x 0 = a} ≃ (K × K) := {
    toFun := fun x => (x.1 1, x.1 2)
    invFun := fun y => ⟨fun i => if i = 0 then a else if i = 1 then y.1 else y.2, by simp⟩
    left_inv := by
      intro x
      apply Subtype.ext
      funext i
      fin_cases i <;> simp [x.2]
    right_inv := by
      intro y
      rcases y with ⟨y₁, y₂⟩
      rfl
  }
  rw [Fintype.card_congr e, Fintype.card_prod]
  simp [pow_two]

/-- Intersecting any subset of `K^3` with one first-coordinate fiber cannot
increase its size beyond the ambient fiber size. This remains true when the
subset is only an `F₂`-subspace and has no `K`-linear structure. -/
theorem card_subset_first_coordinate_fiber_le
    (A : Finset (Fin 3 → K)) (a : K) :
    (A.filter fun x => x 0 = a).card ≤ Fintype.card K ^ 2 := by
  classical
  have hsub : A.filter (fun x => x 0 = a) ⊆
      (Finset.univ.filter fun x : Fin 3 → K => x 0 = a) := by
    intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨Finset.mem_univ _, hx.2⟩
  calc
    (A.filter (fun x => x 0 = a)).card ≤
        (Finset.univ.filter fun x : Fin 3 → K => x 0 = a).card :=
      Finset.card_le_card hsub
    _ = Fintype.card {x : Fin 3 → K // x 0 = a} := by
      symm
      rw [Fintype.card_subtype]
    _ = Fintype.card K ^ 2 := card_first_coordinate_fiber K a

/-- The union of first-coordinate fibers indexed by `D` has at most
`|D| |K|^2` points, even after intersecting with an arbitrary clean set. -/
theorem card_subset_first_coordinate_values_le
    (A : Finset (Fin 3 → K)) (D : Finset K) :
    (A.filter fun x => x 0 ∈ D).card ≤ D.card * Fintype.card K ^ 2 := by
  classical
  have hsub : A.filter (fun x => x 0 ∈ D) ⊆
      (Finset.univ.filter fun x : Fin 3 → K => x 0 ∈ D) := by
    intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨Finset.mem_univ _, hx.2⟩
  have hcard : Fintype.card {x : Fin 3 → K // x 0 ∈ D} =
      D.card * Fintype.card K ^ 2 := by
    let e : {x : Fin 3 → K // x 0 ∈ D} ≃
        ({a : K // a ∈ D} × (K × K)) := {
      toFun := fun x => (⟨x.1 0, x.2⟩, (x.1 1, x.1 2))
      invFun := fun y => ⟨fun i =>
        if i = 0 then y.1.1 else if i = 1 then y.2.1 else y.2.2, by simp⟩
      left_inv := by
        intro x
        apply Subtype.ext
        funext i
        fin_cases i <;> simp
      right_inv := by
        intro y
        rcases y with ⟨⟨a, ha⟩, b, c⟩
        apply Prod.ext
        · apply Subtype.ext
          rfl
        · exact Prod.ext rfl rfl
    }
    rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_subtype]
    simp [pow_two]
  calc
    (A.filter (fun x => x 0 ∈ D)).card ≤
        (Finset.univ.filter fun x : Fin 3 → K => x 0 ∈ D).card :=
      Finset.card_le_card hsub
    _ = Fintype.card {x : Fin 3 → K // x 0 ∈ D} := by
      symm
      rw [Fintype.card_subtype]
    _ = D.card * Fintype.card K ^ 2 := hcard

end

end CorruptedFieldRecovery
