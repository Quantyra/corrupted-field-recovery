import CorruptedFieldRecovery.SamplingCounts
import CorruptedFieldRecovery.ConditionalCounts
import CorruptedFieldRecovery.ProperSubfieldCounts
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic

/-! Finite-count assembly for the four-vector part of the actual trial.

This file keeps the clean set arbitrary: its only source is the binary support
kernel, and no K-linearity is introduced. The basis-triple count and the
basis-relative coordinate transport are separate obligations; the declarations
below assemble a proved per-fiber bound over every successful triple.
-/

namespace CorruptedFieldRecovery

open Module

noncomputable section

local instance subtypeFintypeOfFinite {α : Type*} [Finite α] (p : α → Prop) :
    Fintype {x : α // p x} := Fintype.ofFinite _

/-- Counting principle for the independent fourth draw. `B` is the set of
first-three tuples already certified as a K-basis. For each such tuple,
`goodFourth` contains clean fourth vectors whose first coordinate in that
sampled basis generates K. The finite sigma type is exactly the set of
qualifying clean four-tuples, represented as a triple followed by its fourth
word. -/
theorem card_good_four_tuples_lower
    {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I]
    (B : Finset I) (goodFourth : I → Finset O) (m : ℕ)
    (hfiber : ∀ i ∈ B, m ≤ (goodFourth i).card) :
    m * B.card ≤
      Fintype.card (Σ i : {i // i ∈ B}, {o : O // o ∈ goodFourth i.1}) := by
  classical
  have hsum :
      m * B.card ≤
        ∑ i : {i // i ∈ B}, Fintype.card {o : O // o ∈ goodFourth i.1} := by
    calc
      m * B.card = ∑ _i : {i // i ∈ B}, m := by simp [Nat.mul_comm]
      _ ≤ ∑ i : {i // i ∈ B}, Fintype.card {o : O // o ∈ goodFourth i.1} :=
        Finset.sum_le_sum fun i _ => by
          rw [Fintype.card_coe]
          exact hfiber i.1 i.2
  rw [Fintype.card_sigma]
  exact hsum

/-- Apply the captured arbitrary-subset coordinate-fiber bound to the
fourth clean vector. The coordinate may be supplied by a sampled-basis
equivalence; the theorem does not assume the clean set is K-linear. -/
theorem bad_fourth_coordinate_count_le
    (K : Type*) [Fintype K] [DecidableEq K]
    (A : Finset (Fin 3 → K)) (D : Finset K) :
    (A.filter fun x => x 0 ∈ D).card ≤ D.card * Fintype.card K ^ 2 :=
  card_subset_first_coordinate_values_le K A D

/-! The next lemmas count the first-three basis event by successive K-spans.
The clean set is only a finite subset of the ambient vector space throughout. -/

theorem card_span_finset_le_pow
    {K V : Type*} [Field K] [Fintype K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype V] (s : Finset V) :
    Fintype.card (Submodule.span K (s : Set V)) ≤ Fintype.card K ^ s.card := by
  classical
  letI : Fintype (Submodule.span K (s : Set V)) :=
    Fintype.ofFinite (Submodule.span K (s : Set V))
  rw [Module.card_eq_pow_finrank (K := K) (V := Submodule.span K (s : Set V))]
  apply Nat.pow_le_pow_right Fintype.card_pos
  simpa using (finrank_span_finset_le_card (R := K) s)

private theorem card_clean_predicate
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : Finset V) (p : V → Prop) [DecidablePred p] :
    Fintype.card {x : V // x ∈ A ∧ p x} = (A.filter p).card := by
  classical
  apply Fintype.card_of_subtype (s := A.filter p)
  intro x
  simp [Finset.mem_filter]

theorem card_clean_inter_span_le
    {K V : Type*} [Field K] [Fintype K] [DecidableEq V]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype V]
    (A s : Finset V) :
    Fintype.card {x : V // x ∈ A ∧ x ∈ Submodule.span K (s : Set V)} ≤
      Fintype.card K ^ s.card := by
  classical
  let span := Submodule.span K (s : Set V)
  let f : {x : V // x ∈ A ∧ x ∈ span} → span := fun x => ⟨x.1, x.2.2⟩
  have hinj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    simpa [f] using congrArg Subtype.val h
  have hcard := Fintype.card_le_of_injective f hinj
  have hspan : Fintype.card span ≤ Fintype.card K ^ s.card := by
    simpa [span] using card_span_finset_le_pow (K := K) (V := V) s
  exact hcard.trans hspan

theorem card_clean_avoiding_span_lower
    {K V : Type*} [Field K] [Fintype K] [DecidableEq V]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype V]
    (A s : Finset V) :
    A.card - Fintype.card K ^ s.card ≤
      Fintype.card {x : V // x ∈ A ∧ x ∉ Submodule.span K (s : Set V)} := by
  classical
  let p : V → Prop := fun x => x ∈ Submodule.span K (s : Set V)
  letI : DecidablePred p := Classical.decPred p
  letI : DecidablePred (fun x => ¬ p x) := Classical.decPred _
  have hsplit := Finset.card_filter_add_card_filter_not (s := A) p
  have hbad : (A.filter p).card ≤ Fintype.card K ^ s.card := by
    have hc := card_clean_inter_span_le (K := K) (V := V) A s
    have heq : Fintype.card {x : V // x ∈ A ∧ p x} = (A.filter p).card :=
      card_clean_predicate A p
    rw [← heq]
    exact hc
  have hgood : Fintype.card {x : V // x ∈ A ∧ ¬ p x} = (A.filter fun x => ¬ p x).card :=
    card_clean_predicate A (fun x => ¬ p x)
  change A.card - Fintype.card K ^ s.card ≤ Fintype.card {x : V // x ∈ A ∧ ¬ p x}
  rw [hgood]
  omega

abbrev CleanFirst {K : Type*} [Field K] [Fintype K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Fintype V] (A : Finset V) :=
  {x : V // x ∈ A ∧ x ≠ 0}

abbrev CleanSecond {K : Type*} [Field K] [Fintype K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Fintype V] [DecidableEq V] (A : Finset V) :=
  Σ x : CleanFirst (K := K) A,
    {y : V // y ∈ A ∧
      y ∉ Submodule.span K (({(x.1 : V)} : Finset V) : Set V)}

abbrev CleanBasisTriple {K : Type*} [Field K] [Fintype K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Fintype V] [DecidableEq V] (A : Finset V) :=
  Σ xy : CleanSecond (K := K) A,
    {z : V // z ∈ A ∧
      z ∉ Submodule.span K
        (({(xy.1.1 : V), (xy.2.1 : V)} : Finset V) : Set V)}

private theorem card_sigma_fiber_lower
    {I : Type*} [Fintype I] {F : I → Type*} [∀ i, Fintype (F i)]
    (m : ℕ) (h : ∀ i, m ≤ Fintype.card (F i)) :
    m * Fintype.card I ≤ Fintype.card (Σ i, F i) := by
  classical
  rw [Fintype.card_sigma]
  calc
    m * Fintype.card I = ∑ _i : I, m := by simp [Nat.mul_comm]
    _ ≤ ∑ i : I, Fintype.card (F i) :=
      Finset.sum_le_sum fun i _ => h i

/-- The actual ordered first-three sample count, expressed as a nested finite
type. `x₁` avoids zero, `x₂` avoids the K-span of `x₁`, and `x₃` avoids the
K-span of `x₁,x₂`. These are exactly the successive conditions for a sampled
K-basis in dimension three. No K-linearity of `A` is assumed. -/
theorem card_clean_basis_triples_lower
    {K V : Type*} [Field K] [Fintype K] [DecidableEq V]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype V]
    (A : Finset V) :
    (A.card - Fintype.card K ^ 2) *
        ((A.card - Fintype.card K) * (A.card - 1)) ≤
      Fintype.card (CleanBasisTriple (K := K) A) := by
  classical
  let First := CleanFirst (K := K) A
  let Second := CleanSecond (K := K) A
  let Triple := CleanBasisTriple (K := K) A
  have hfirst : A.card - 1 ≤ Fintype.card First := by
    letI : DecidablePred (fun x : V => x ≠ 0) := Classical.decPred _
    have hcard : Fintype.card First = (A.filter fun x => x ≠ 0).card := by
      exact card_clean_predicate A (fun x => x ≠ 0)
    have hz : (A.filter fun x => x = 0).card ≤ 1 := by
      calc
        (A.filter fun x => x = 0).card ≤ ({0} : Finset V).card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_filter] at hx
          exact Finset.mem_singleton.mpr hx.2
        _ = 1 := by simp
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := A) (fun x : V => x = 0)
    have hsplit' : (A.filter fun x => x = 0).card +
        (A.filter fun x => x ≠ 0).card = A.card := by
      simpa using hsplit
    rw [hcard]
    omega
  have hsecond : (A.card - Fintype.card K) * Fintype.card First ≤
      Fintype.card Second := by
    letI : ∀ x : First, Fintype
        {y : V // y ∈ A ∧
          y ∉ Submodule.span K (({(x.1 : V)} : Finset V) : Set V)} :=
      fun _ => Fintype.ofFinite _
    apply card_sigma_fiber_lower
    intro x
    have h := card_clean_avoiding_span_lower (K := K) (V := V) A ({x.1} : Finset V)
    simp only [Finset.card_singleton, pow_one] at h
    exact h
  have hthird : (A.card - Fintype.card K ^ 2) * Fintype.card Second ≤
      Fintype.card Triple := by
    letI : ∀ xy : Second, Fintype
        {z : V // z ∈ A ∧
          z ∉ Submodule.span K
            (({(xy.1.1 : V), (xy.2.1 : V)} : Finset V) : Set V)} :=
      fun _ => Fintype.ofFinite _
    apply card_sigma_fiber_lower
    intro xy
    have h := card_clean_avoiding_span_lower (K := K) (V := V) A
      ({xy.1.1, xy.2.1} : Finset V)
    have hpair : ({xy.1.1, xy.2.1} : Finset V).card ≤ 2 := Finset.card_le_two
    have hpow : Fintype.card K ^ ({xy.1.1, xy.2.1} : Finset V).card ≤
        Fintype.card K ^ 2 := Nat.pow_le_pow_right Fintype.card_pos hpair
    have h' : A.card - Fintype.card K ^ 2 ≤
        Fintype.card {z : V // z ∈ A ∧
          z ∉ Submodule.span K
            (({(xy.1.1 : V), (xy.2.1 : V)} : Finset V) : Set V)} := by
      exact (Nat.sub_le_sub_left hpow A.card).trans h
    exact h'
  have hmul : (A.card - Fintype.card K ^ 2) *
      ((A.card - Fintype.card K) * (A.card - 1)) ≤
        (A.card - Fintype.card K ^ 2) *
          ((A.card - Fintype.card K) * Fintype.card First) := by
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hfirst)
  calc
    (A.card - Fintype.card K ^ 2) *
        ((A.card - Fintype.card K) * (A.card - 1)) ≤
      (A.card - Fintype.card K ^ 2) *
        ((A.card - Fintype.card K) * Fintype.card First) := hmul
    _ ≤ (A.card - Fintype.card K ^ 2) * Fintype.card Second :=
      Nat.mul_le_mul_left _ hsecond
    _ ≤ Fintype.card Triple := hthird

/-- Forget the cleanliness proofs in the nested basis-frame count and recover
the four coordinate slots of the physical sampler. -/
def cleanBasisTripleVectors
    {K V : Type*} [Field K] [Fintype K] [DecidableEq V]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype V]
    {A : Finset V} (t : CleanBasisTriple (K := K) A) : Fin 3 → V :=
  Fin.snoc (Fin.snoc (fun _ : Fin 1 => t.1.1.1) t.1.2.1) t.2.1

/-- The sequential span-avoidance predicate counted above is exactly linear
independence of the first three sampled vectors. This is the bridge from the
successive forbidden-span count to the sampler's basis event. -/
theorem clean_basis_triple_linearIndependent
    {K V : Type*} [Field K] [Fintype K] [DecidableEq V]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype V]
    {A : Finset V} (t : CleanBasisTriple (K := K) A) :
    LinearIndependent K (cleanBasisTripleVectors t) := by
  let v0 := t.1.1.1
  let v1 := t.1.2.1
  let v2 := t.2.1
  have h0 : LinearIndependent K (fun _ : Fin 1 => v0) := by
    apply linearIndependent_unique_iff.mpr
    simpa [v0] using t.1.1.2.2
  have h1 : v1 ∉ Submodule.span K (Set.range (fun _ : Fin 1 => v0)) := by
    simpa [v0, v1] using t.1.2.2.2
  have h01 : LinearIndependent K (Fin.snoc (fun _ : Fin 1 => v0) v1) :=
    h0.finSnoc h1
  have h2 : v2 ∉ Submodule.span K
      (Set.range (Fin.snoc (fun _ : Fin 1 => v0) v1)) := by
    simpa [v0, v1, v2, Fin.snoc, Set.pair_comm] using t.2.2.2
  simpa [cleanBasisTripleVectors, v0, v1, v2] using h01.finSnoc h2

/-- In a three-dimensional K-space, every counted sequential frame determines
the unique sampled basis used by the fourth-vector coordinate test. -/
noncomputable def cleanBasisTripleBasis
    {K V : Type*} [Field K] [Fintype K] [DecidableEq V]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype V]
    {A : Finset V} (t : CleanBasisTriple (K := K) A)
    (hdim : finrank K V = 3) : Basis (Fin 3) K V := by
  let v := cleanBasisTripleVectors t
  have hli : LinearIndependent K v := clean_basis_triple_linearIndependent t
  have hspanrank : finrank K (Submodule.span K (Set.range v)) = 3 := by
    have h := (linearIndependent_iff_card_eq_finrank_span (R := K)).mp hli
    have h' : Fintype.card (Fin 3) = finrank K (Submodule.span K (Set.range v)) := by
      simpa [Set.finrank] using h
    simpa using h'.symm
  have htop : Submodule.span K (Set.range v) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (hspanrank.trans hdim.symm)
  exact Basis.mk hli htop.ge

/-- The first-four-word contribution to the unconditional five-word count.
`m` is a uniform lower bound on good fourth clean vectors for every good
basis triple. Multiplying this count by `g` later accounts for the independent
fifth scalar word; no conditional probability or independence claim is hidden
in this finite cardinality statement. -/
theorem card_good_five_word_pairs_lower
    {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I]
    (B : Finset I) (goodFourth : I → Finset O) (m g : ℕ)
    (hfiber : ∀ i ∈ B, m ≤ (goodFourth i).card) :
    (m * B.card) * g ≤
      Fintype.card (Σ i : {i // i ∈ B},
        ({o : O // o ∈ goodFourth i.1} × Fin g)) := by
  classical
  rw [Fintype.card_sigma]
  have hsum :
      (m * B.card) * g ≤
        ∑ i : {i // i ∈ B},
          Fintype.card ({o : O // o ∈ goodFourth i.1} × Fin g) := by
    calc
      (m * B.card) * g =
          ∑ _i : {i // i ∈ B}, m * g := by simp [Nat.mul_assoc, Nat.mul_left_comm]
      _ ≤ ∑ i : {i // i ∈ B},
          Fintype.card {o : O // o ∈ goodFourth i.1} * g :=
        Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right g (by
          rw [Fintype.card_coe]
          exact hfiber i.1 i.2)
      _ = ∑ i : {i // i ∈ B},
          Fintype.card ({o : O // o ∈ goodFourth i.1} × Fin g) := by
        simp [Fintype.card_prod]
  exact hsum

end

end CorruptedFieldRecovery
