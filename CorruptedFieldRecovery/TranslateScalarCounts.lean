import Mathlib.Data.Finset.Card
import Mathlib.Algebra.CharP.Two
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic

/-! Finite root counts for the fifth-word translate scalar.

The support is represented here by its actual finite set of K³ coordinates.
No K-linearity of this set is used: its binary-subspace structure enters only
through its cardinality in the caller. -/

namespace CorruptedFieldRecovery

noncomputable section

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]

abbrev KTriple := Fin 3 → K

def translateScalarRoots (u₀ u₁ : KTriple K) : Finset K :=
  Finset.univ.filter fun t => u₀ + t • u₁ = 0

theorem card_translateScalarRoots_le_one (u₀ u₁ : KTriple K)
    (hu₁ : u₁ ≠ 0) : (translateScalarRoots K u₀ u₁).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro t ht u hu
  simp only [translateScalarRoots, Finset.mem_filter, Finset.mem_univ,
    true_and] at ht hu
  have hmul : (t - u) • u₁ = 0 := by
    have heq : t • u₁ = u • u₁ := by
      exact add_left_cancel (ht.trans hu.symm)
    rw [sub_smul, heq, sub_self]
  have hj : ∃ j : Fin 3, u₁ j ≠ 0 := by
    by_contra h
    push Not at h
    apply hu₁
    funext j
    exact h j
  obtain ⟨j, hj⟩ := hj
  have hcoord := congrFun hmul j
  simp only [Pi.smul_apply, smul_eq_mul] at hcoord
  have htu : t - u = 0 := (mul_eq_zero.mp hcoord).resolve_right hj
  exact sub_eq_zero.mp htu

abbrev TranslatePair (U : Finset (KTriple K)) :=
  {x // x ∈ U} × {x // x ∈ U}

def nonzeroTranslatePairs (U : Finset (KTriple K)) : Finset (TranslatePair K U) :=
  Finset.univ.filter fun p => p.1.1 ≠ 0 ∨ p.2.1 ≠ 0

def badTranslateScalars (U : Finset (KTriple K)) : Finset K :=
  (nonzeroTranslatePairs K U).biUnion fun p =>
    translateScalarRoots K p.1.1 p.2.1

def translateActionGood (U : Finset (KTriple K)) (t : K) : Prop :=
  (∀ u₁, u₁ ∈ U → t • u₁ = 0 → u₁ = 0) ∧
  (∀ u₀, u₀ ∈ U → ∀ u₁, u₁ ∈ U → u₀ ≠ 0 → u₀ + t • u₁ ≠ 0)

theorem mem_badTranslateScalars_iff (U : Finset (KTriple K)) (t : K) :
    t ∈ badTranslateScalars K U ↔
      ∃ u₀ ∈ U, ∃ u₁ ∈ U,
        (u₀ ≠ 0 ∨ u₁ ≠ 0) ∧ u₀ + t • u₁ = 0 := by
  simp [badTranslateScalars, nonzeroTranslatePairs, translateScalarRoots,
    Finset.mem_biUnion, Finset.mem_filter, and_left_comm, and_comm]

theorem mem_badTranslateScalars_iff_not_good
    (U : Finset (KTriple K)) (t : K)
    (hzero : (0 : KTriple K) ∈ U) :
    t ∈ badTranslateScalars K U ↔ ¬ translateActionGood K U t := by
  classical
  rw [mem_badTranslateScalars_iff]
  constructor
  · rintro ⟨u₀, hu₀, u₁, hu₁, hne, hrel⟩ hgood
    by_cases hu₀ne : u₀ ≠ 0
    · exact hgood.2 u₀ hu₀ u₁ hu₁ hu₀ne hrel
    · have hu₀zero : u₀ = 0 := not_ne_iff.mp hu₀ne
      have htzero : t • u₁ = 0 := by simpa [hu₀zero] using hrel
      exact (hne.resolve_left hu₀ne) (hgood.1 u₁ hu₁ htzero)
  · intro hbad
    by_contra hnotBad
    apply hbad
    constructor
    · intro u₁ hu₁ htzero
      by_contra hu₁ne
      apply hnotBad
      refine ⟨0, hzero, u₁, hu₁, Or.inr hu₁ne, ?_⟩
      simp [htzero]
    · intro u₀ hu₀ u₁ hu₁ hu₀ne hrel
      apply hnotBad
      exact ⟨u₀, hu₀, u₁, hu₁, Or.inl hu₀ne, hrel⟩

omit [Fintype K] in
theorem card_nonzeroTranslatePairs_le (U : Finset (KTriple K))
    (hzero : (0 : KTriple K) ∈ U) :
    (nonzeroTranslatePairs K U).card ≤ U.card ^ 2 - 1 := by
  classical
  let p : TranslatePair K U → Prop := fun x => x.1.1 ≠ 0 ∨ x.2.1 ≠ 0
  letI : DecidablePred p := Classical.decPred p
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (TranslatePair K U))) p
  have hzeroCard : (Finset.univ.filter fun x : TranslatePair K U => ¬ p x).card = 1 := by
    have hsingleton : (Finset.univ.filter fun x : TranslatePair K U => ¬ p x) =
        {⟨⟨0, hzero⟩, ⟨0, hzero⟩⟩} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · intro hx
        have hx' := not_or.mp hx
        apply Prod.ext
        · apply Subtype.ext
          exact not_not.mp hx'.1
        · apply Subtype.ext
          exact not_not.mp hx'.2
      · intro hx
        subst x
        simp [p]
    rw [hsingleton]
    simp
  have hprod : Fintype.card (TranslatePair K U) = U.card ^ 2 := by
    simp only [TranslatePair, Fintype.card_prod, Fintype.card_coe, pow_two]
  have hsplit' : (nonzeroTranslatePairs K U).card + 1 = U.card ^ 2 := by
    rw [hzeroCard] at hsplit
    simpa [nonzeroTranslatePairs, p, hprod] using hsplit
  omega

theorem card_badTranslateScalars_le (U : Finset (KTriple K))
    (hzero : (0 : KTriple K) ∈ U) :
    (badTranslateScalars K U).card ≤ U.card ^ 2 - 1 := by
  classical
  calc
    (badTranslateScalars K U).card ≤
        ∑ p ∈ nonzeroTranslatePairs K U,
          (translateScalarRoots K p.1.1 p.2.1).card := Finset.card_biUnion_le
    _ ≤ (nonzeroTranslatePairs K U).card := by
      calc
        _ ≤ ∑ p ∈ nonzeroTranslatePairs K U, 1 := by
          apply Finset.sum_le_sum
          intro p hp
          have hne : p.1.1 ≠ 0 ∨ p.2.1 ≠ 0 := (Finset.mem_filter.mp hp).2
          by_cases hu₁ : p.2.1 ≠ 0
          · exact card_translateScalarRoots_le_one K p.1.1 p.2.1 hu₁
          · have hu₀ : p.1.1 ≠ 0 := hne.resolve_right hu₁
            have hu₁zero : p.2.1 = 0 := not_not.mp hu₁
            have hempty : translateScalarRoots K p.1.1 p.2.1 = ∅ := by
              ext t
              simp [translateScalarRoots, hu₁zero, hu₀]
            simp [hempty]
        _ = (nonzeroTranslatePairs K U).card := by simp
    _ ≤ U.card ^ 2 - 1 := by
      simpa [nonzeroTranslatePairs] using card_nonzeroTranslatePairs_le K U hzero

theorem card_badTranslateScalars_le_pow (U : Finset (KTriple K))
    (hzero : (0 : KTriple K) ∈ U) (r : Nat) (hcard : U.card = 2 ^ r) :
    (badTranslateScalars K U).card ≤ 2 ^ (2 * r) - 1 := by
  have h := card_badTranslateScalars_le K U hzero
  rw [hcard] at h
  simpa [pow_mul, Nat.mul_comm] using h

variable [Algebra (ZMod 2) K]

noncomputable def supportCoordinateFinset
    (U : Submodule (ZMod 2) (KTriple K)) : Finset (KTriple K) := by
  classical
  exact Finset.univ.map ⟨fun u : U => (u : KTriple K), Subtype.val_injective⟩

omit [DecidableEq K] in
theorem mem_supportCoordinateFinset_iff
    (U : Submodule (ZMod 2) (KTriple K)) (x : KTriple K) :
    x ∈ supportCoordinateFinset K U ↔ x ∈ U := by
  classical
  constructor
  · intro hx
    rcases Finset.mem_map.mp hx with ⟨u, hu, rfl⟩
    exact u.2
  · intro hx
    apply Finset.mem_map.mpr
    exact ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩

omit [DecidableEq K] in
theorem card_supportCoordinateFinset
    (U : Submodule (ZMod 2) (KTriple K)) :
    (supportCoordinateFinset K U).card =
      2 ^ Module.finrank (ZMod 2) U := by
  classical
  rw [supportCoordinateFinset, Finset.card_map]
  rw [Finset.card_univ, Module.card_eq_pow_finrank (K := ZMod 2) (V := U)]
  norm_num

theorem card_badTranslateScalars_submodule_le
    (U : Submodule (ZMod 2) (KTriple K)) :
    (badTranslateScalars K (supportCoordinateFinset K U)).card ≤
      2 ^ (2 * Module.finrank (ZMod 2) U) - 1 := by
  apply card_badTranslateScalars_le_pow
  · exact (mem_supportCoordinateFinset_iff K U 0).2 (Submodule.zero_mem U)
  · rw [card_supportCoordinateFinset]

omit [DecidableEq K] in
theorem scalarAction_injective_subtype_iff
    (U : Submodule (ZMod 2) (KTriple K)) (t : K) :
    Function.Injective (fun u : U => t • (u : KTriple K)) ↔
      ∀ x ∈ supportCoordinateFinset K U, t • x = 0 → x = 0 := by
  classical
  constructor
  · intro hinj x hx htx
    have hxU := (mem_supportCoordinateFinset_iff K U x).1 hx
    have heq : (⟨x, hxU⟩ : U) = 0 := by
      apply hinj
      change t • x = t • (0 : KTriple K)
      simpa using htx
    exact congrArg Subtype.val heq
  · intro hker x y hxy
    apply Subtype.ext
    have hdiffU : x.1 - y.1 ∈ U := U.sub_mem x.2 y.2
    change t • (x.1 : KTriple K) = t • (y.1 : KTriple K) at hxy
    have hdiff : t • (x.1 - y.1) = 0 := by
      rw [smul_sub, hxy]
      simp
    have hzero := hker (x.1 - y.1)
      ((mem_supportCoordinateFinset_iff K U (x.1 - y.1)).2 hdiffU) hdiff
    exact sub_eq_zero.mp hzero

def translateOverlapTrivial
    (U : Submodule (ZMod 2) (KTriple K)) (t : K) : Prop :=
  ∀ u₀, u₀ ∈ U → ∀ u₁, u₁ ∈ U → t • u₁ = u₀ → u₀ = 0

omit [Fintype K] [DecidableEq K] [Algebra (ZMod 2) K] in
theorem charTwo_sum_eq_zero_iff {x y : KTriple K} [CharP K 2] :
    x + y = 0 ↔ y = x := by
  constructor
  · intro h
    funext i
    exact (CharTwo.add_eq_zero.mp (congrFun h i)).symm
  · intro h
    funext i
    exact CharTwo.add_eq_zero.mpr (congrFun h i).symm

theorem translateActionGood_submodule_iff
    (U : Submodule (ZMod 2) (KTriple K)) (t : K) [CharP K 2] :
    translateActionGood K (supportCoordinateFinset K U) t ↔
      Function.Injective (fun u : U => t • (u : KTriple K)) ∧
        translateOverlapTrivial K U t := by
  constructor
  · intro h
    constructor
    · exact (scalarAction_injective_subtype_iff K U t).2 h.1
    · intro u₀ hu₀ u₁ hu₁ hact
      have hrel : u₀ + t • u₁ = 0 :=
        (charTwo_sum_eq_zero_iff (x := u₀) (y := t • u₁)).2 hact
      by_cases hu₀zero : u₀ = 0
      · exact hu₀zero
      · exact (h.2 u₀ ((mem_supportCoordinateFinset_iff K U u₀).2 hu₀)
          u₁ ((mem_supportCoordinateFinset_iff K U u₁).2 hu₁) hu₀zero hrel).elim
  · rintro ⟨hinj, hoverlap⟩
    constructor
    · exact (scalarAction_injective_subtype_iff K U t).1 hinj
    · intro u₀ hu₀ u₁ hu₁ hu₀ne hrel
      have hact : t • u₁ = u₀ :=
        (charTwo_sum_eq_zero_iff (x := u₀) (y := t • u₁)).1 hrel
      exact hu₀ne (hoverlap u₀ ((mem_supportCoordinateFinset_iff K U u₀).1 hu₀)
        u₁ ((mem_supportCoordinateFinset_iff K U u₁).1 hu₁) hact)

end

end CorruptedFieldRecovery
