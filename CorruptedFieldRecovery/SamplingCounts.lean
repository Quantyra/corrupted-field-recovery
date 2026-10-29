import CorruptedFieldRecovery.BinaryTensor
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

noncomputable section

local instance : Fintype (ZMod 2) := Fintype.ofFinite (ZMod 2)

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

/- The predicate form makes the four-word count apply directly to the kernel
of the physical support map. -/
theorem card_four_words_for_predicate
    {V : Type*} [Fintype V] {p : V → Prop} [DecidablePred p] :
    Fintype.card {x : Fin 4 → V // ∀ i, p (x i)} =
      (Fintype.card {v // p v} : ℕ) ^ 4 := by
  let e : {x : Fin 4 → V // ∀ i, p (x i)} ≃ (Fin 4 → {v // p v}) := {
    toFun := fun x i => ⟨x.1 i, x.2 i⟩
    invFun := fun x => ⟨fun i => (x i).1, fun i => (x i).2⟩
    left_inv := by intro x; apply Subtype.ext; rfl
    right_inv := by intro x; funext i; apply Subtype.ext; rfl
  }
  calc
    Fintype.card {x : Fin 4 → V // ∀ i, p (x i)} =
        Fintype.card (Fin 4 → {v // p v}) := Fintype.card_congr e
    _ = (Fintype.card {v // p v} : ℕ) ^ 4 := by simp

/- For the manuscript's actual binary input space, a surjective support map
to an r-bit coordinate space has a clean four-word count of 2^(4(n-r)).
Multiplying by 2^(4R) bounds it below by the full 4n-bit sample space when
r ≤ R, deriving the clean-event lower bound from finite counts. -/
theorem four_word_clean_count_binary
    {n r R : ℕ} (u : BinaryVector n →ₗ[ZMod 2] BinaryVector r)
    (hu : Function.Surjective u) (hr : r ≤ R) :
    (Fintype.card {x : Fin 4 → BinaryVector n // ∀ i, u (x i) = 0} =
        2 ^ (4 * (n - r))) ∧
      (Fintype.card {x : Fin 4 → BinaryVector n // ∀ i, u (x i) = 0} *
          2 ^ (4 * R) ≥ Fintype.card (Fin 4 → BinaryVector n)) := by
  classical
  have hdimV : finrank (ZMod 2) (BinaryVector n) = n := by
    rw [Module.finrank_eq_card_basis (Pi.basisFun (ZMod 2) (Fin n))]
    simp
  have hdimW : finrank (ZMod 2) (BinaryVector r) = r := by
    rw [Module.finrank_eq_card_basis (Pi.basisFun (ZMod 2) (Fin r))]
    simp
  have hdim := u.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hu, finrank_top, hdimW, hdimV] at hdim
  have hrn : r ≤ n := by omega
  have hcardV : Fintype.card (BinaryVector n) = 2 ^ n := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := BinaryVector n), hdimV]
    norm_num
  have hker := card_ker_support_f2 u hu n r hdimV hdimW
  have hkerFintype : Fintype.card (LinearMap.ker u) = 2 ^ (n - r) := by
    rw [← Nat.card_eq_fintype_card, hker]
  have hsubtype : Fintype.card {v : BinaryVector n // u v = 0} =
      Fintype.card (LinearMap.ker u) := by
    apply Fintype.card_congr
    exact {
      toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro x; apply Subtype.ext; rfl
    }
  have hclean : Fintype.card
      {x : Fin 4 → BinaryVector n // ∀ i, u (x i) = 0} =
        2 ^ (4 * (n - r)) := by
    rw [card_four_words_for_predicate
      (p := fun v : BinaryVector n => u v = 0), hsubtype, hkerFintype]
    rw [← pow_mul]
    congr 1
    omega
  have htotal : Fintype.card (Fin 4 → BinaryVector n) = 2 ^ (4 * n) := by
    rw [Fintype.card_fun, Fintype.card_fin, hcardV]
    rw [← pow_mul]
    congr 1
    omega
  have hpow : 4 * (n - r) + 4 * R ≥ 4 * n := by omega
  refine ⟨hclean, ?_⟩
  rw [hclean, htotal, ← pow_add]
  exact Nat.pow_le_pow_right (by decide) hpow

end

end CorruptedFieldRecovery
