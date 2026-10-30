import CorruptedFieldRecovery.ProbabilityAssembly
import CorruptedFieldRecovery.ProbabilityBasisTransport
import Mathlib.Data.Finset.Sigma
import Mathlib.Tactic

/-! Canonical-Finset assembly of the first four draws. All sample outcomes are
raw vectors in Finsets and Finset sigma products; no Fintype is chosen for a
proof-carrying subtype. -/

namespace CorruptedFieldRecovery

open Module

noncomputable section

private theorem card_clean_inter_span_finset_le
    {K V : Type*} [Field K] [Fintype K] [DecidableEq V]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype V]
    (A s : Finset V)
    [DecidablePred (fun x : V => x ∈ Submodule.span K (s : Set V))] :
    (A.filter fun x => x ∈ Submodule.span K (s : Set V)).card ≤
      Fintype.card K ^ s.card := by
  classical
  let S := A.filter fun x => x ∈ Submodule.span K (s : Set V)
  let f : {x // x ∈ S} → Submodule.span K (s : Set V) := fun x =>
    ⟨x.1, (Finset.mem_filter.mp x.2).2⟩
  have hinj : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    simpa [f] using congrArg Subtype.val h
  calc
    S.card = Fintype.card {x // x ∈ S} := by simp [Fintype.card_coe]
    _ ≤ Fintype.card (Submodule.span K (s : Set V)) :=
      Fintype.card_le_of_injective f hinj
    _ ≤ Fintype.card K ^ s.card := by
      rw [Module.card_eq_pow_finrank (K := K) (V := Submodule.span K (s : Set V))]
      apply Nat.pow_le_pow_right Fintype.card_pos
      simpa using (finrank_span_finset_le_card (R := K) s)

private theorem card_clean_avoiding_span_finset_lower
    {K V : Type*} [Field K] [Fintype K] [DecidableEq V]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype V]
    (A s : Finset V)
    [DecidablePred (fun x : V => x ∉ Submodule.span K (s : Set V))] :
    A.card - Fintype.card K ^ s.card ≤
      (A.filter fun x => x ∉ Submodule.span K (s : Set V)).card := by
  classical
  let p : V → Prop := fun x => x ∈ Submodule.span K (s : Set V)
  letI : DecidablePred p := Classical.decPred p
  have hsplit := Finset.card_filter_add_card_filter_not (s := A) p
  have hbad := card_clean_inter_span_finset_le (K := K) (V := V) A s
  have hbad' : (A.filter p).card ≤ Fintype.card K ^ s.card := by
    simpa [p] using hbad
  change A.card - Fintype.card K ^ s.card ≤ (A.filter fun x => ¬ p x).card
  omega

private theorem card_sigma_finset
    {I : Type*} {O : I → Type*} (s : Finset I)
    (f : ∀ i, Finset (O i)) :
    (s.sigma f).card = ∑ i ∈ s, (f i).card := by
  classical
  simp [Finset.sigma, Multiset.card_sigma]

private theorem card_sigma_finset_lower
    {I : Type*} {O : I → Type*} (s : Finset I)
    (f : ∀ i, Finset (O i)) (m : ℕ)
    (h : ∀ i ∈ s, m ≤ (f i).card) :
    m * s.card ≤ (s.sigma f).card := by
  classical
  rw [card_sigma_finset]
  calc
    m * s.card = ∑ i ∈ s, m := by simp [Nat.mul_comm]
    _ ≤ ∑ i ∈ s, (f i).card :=
      Finset.sum_le_sum fun i hi => h i hi

private def nonzeroCleanSet {K : Type*} [Field K] [Fintype K]
    {V : Type*} [DecidableEq V] [Zero V] (A : Finset V) : Finset V :=
  A.filter fun x => x ≠ 0

private noncomputable def cleanPairSet {K : Type*} [Field K] [Fintype K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Fintype V] [DecidableEq V] (A : Finset V) : Finset (Σ _x : V, V) := by
  classical
  exact (nonzeroCleanSet (K := K) A).sigma fun x =>
    A.filter fun y => y ∉ Submodule.span K (({x} : Finset V) : Set V)

noncomputable def cleanFrameSet {K : Type*} [Field K] [Fintype K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Fintype V] [DecidableEq V] (A : Finset V) :
    Finset (Σ _xy : (Σ _x : V, V), V) := by
  classical
  exact (cleanPairSet (K := K) A).sigma fun xy =>
    A.filter fun z =>
      z ∉ Submodule.span K (({xy.1, xy.2} : Finset V) : Set V)

private theorem fieldTripleFinrankCanonical (K : Type*) [Field K] :
    finrank K (FieldTriple K) = 3 := by
  simp [FieldTriple, Module.finrank_prod]

/-- The exact first-three draw count, as a canonical Finset of raw vectors.
The nested sigma has no extra proof witnesses: each element is one ordered
triple of clean vectors passing the successive K-span tests. -/
theorem card_clean_frame_finset_lower
    (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (A : Finset (FieldTriple K)) :
    (A.card - Fintype.card K ^ 2) *
      ((A.card - Fintype.card K) * (A.card - 1)) ≤
        (cleanFrameSet (K := K) A).card := by
  classical
  let A0 := nonzeroCleanSet (K := K) A
  let P := cleanPairSet (K := K) A
  let T := cleanFrameSet (K := K) A
  have hzero : (A.filter fun x : FieldTriple K => x = 0).card ≤ 1 := by
    calc
      (A.filter fun x => x = 0).card ≤ ({0} : Finset (FieldTriple K)).card := by
        apply Finset.card_le_card
        intro x hx
        exact Finset.mem_singleton.mpr (Finset.mem_filter.mp hx).2
      _ = 1 := by simp
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := A) (fun x : FieldTriple K => x = 0)
  have hsplit' : (A.filter fun x : FieldTriple K => x = 0).card + A0.card = A.card := by
    simpa [A0, nonzeroCleanSet] using hsplit
  have hfirst : A.card - 1 ≤ A0.card := by omega
  have hpair : (A.card - Fintype.card K) * A0.card ≤ P.card := by
    change (A.card - Fintype.card K) * A0.card ≤
      (A0.sigma fun x => A.filter fun y : FieldTriple K =>
        y ∉ Submodule.span K (({x} : Finset (FieldTriple K)) : Set (FieldTriple K))).card
    apply card_sigma_finset_lower A0
      (fun x => A.filter fun y : FieldTriple K =>
        y ∉ Submodule.span K (({x} : Finset (FieldTriple K)) : Set (FieldTriple K)))
      (A.card - Fintype.card K)
    intro x hx
    simpa [Finset.card_singleton, pow_one] using
      (card_clean_avoiding_span_finset_lower (K := K) (V := FieldTriple K)
        A ({x} : Finset (FieldTriple K)))
  have hframe : (A.card - Fintype.card K ^ 2) * P.card ≤ T.card := by
    change (A.card - Fintype.card K ^ 2) * P.card ≤
      (P.sigma fun xy => A.filter fun z : FieldTriple K =>
        z ∉ Submodule.span K
          (({xy.1, xy.2} : Finset (FieldTriple K)) : Set (FieldTriple K))).card
    apply card_sigma_finset_lower P
      (fun xy => A.filter fun z : FieldTriple K =>
        z ∉ Submodule.span K
          (({xy.1, xy.2} : Finset (FieldTriple K)) : Set (FieldTriple K)))
      (A.card - Fintype.card K ^ 2)
    intro xy hxy
    have h := card_clean_avoiding_span_finset_lower (K := K) (V := FieldTriple K)
      A ({xy.1, xy.2} : Finset (FieldTriple K))
    have hpairCard : ({xy.1, xy.2} : Finset (FieldTriple K)).card ≤ 2 :=
      Finset.card_le_two
    have hpow : Fintype.card K ^ ({xy.1, xy.2} : Finset (FieldTriple K)).card ≤
        Fintype.card K ^ 2 := Nat.pow_le_pow_right Fintype.card_pos hpairCard
    exact (Nat.sub_le_sub_left hpow A.card).trans h
  calc
    (A.card - Fintype.card K ^ 2) *
        ((A.card - Fintype.card K) * (A.card - 1)) ≤
      (A.card - Fintype.card K ^ 2) *
        ((A.card - Fintype.card K) * A0.card) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hfirst)
    _ ≤ (A.card - Fintype.card K ^ 2) * P.card := Nat.mul_le_mul_left _ hpair
    _ ≤ T.card := hframe

private def frameWitness
    (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (A : Finset (FieldTriple K))
    (fr : Σ _xy : (Σ _x : FieldTriple K, FieldTriple K), FieldTriple K)
    (hfr : fr ∈ cleanFrameSet (K := K) A) : CleanBasisTriple (K := K) A := by
  classical
  have hparts := Finset.mem_sigma.mp hfr
  have hp := Finset.mem_sigma.mp hparts.1
  have hx := Finset.mem_filter.mp hp.1
  have hy := Finset.mem_filter.mp hp.2
  have hz := Finset.mem_filter.mp hparts.2
  exact ⟨⟨⟨fr.1.1, ⟨hx.1, hx.2⟩⟩,
    ⟨fr.1.2, ⟨hy.1, hy.2⟩⟩⟩, ⟨fr.2, ⟨hz.1, hz.2⟩⟩⟩

private noncomputable def frameBasis
    (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (A : Finset (FieldTriple K))
    (fr : Σ _xy : (Σ _x : FieldTriple K, FieldTriple K), FieldTriple K) :
    Basis (Fin 3) K (FieldTriple K) := by
  classical
  exact if hfr : fr ∈ cleanFrameSet (K := K) A then
    cleanBasisTripleBasis (frameWitness K A fr hfr) (fieldTripleFinrankCanonical K)
  else fieldTripleStandardBasis K

/-- The deterministic basis selected from a clean first-three frame. On a
member of `cleanFrameSet`, this is exactly the basis induced by those three
sampled vectors; outside that event it is the fixed standard basis. -/
noncomputable def canonicalGoodFrameBasis
    (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (A : Finset (FieldTriple K))
    (fr : Σ _xy : (Σ _x : FieldTriple K, FieldTriple K), FieldTriple K) :
    Basis (Fin 3) K (FieldTriple K) :=
  frameBasis K A fr

theorem canonicalGoodFrameBasis_eq_cleanBasisTripleBasis
    (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (A : Finset (FieldTriple K))
    (fr : Σ _xy : (Σ _x : FieldTriple K, FieldTriple K), FieldTriple K)
    (hfr : fr ∈ cleanFrameSet (K := K) A) :
    canonicalGoodFrameBasis K A fr =
      cleanBasisTripleBasis (frameWitness K A fr hfr) (fieldTripleFinrankCanonical K) := by
  simp [canonicalGoodFrameBasis, frameBasis, hfr]

noncomputable def goodFourthFinset
    (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (A : Finset (FieldTriple K)) (D : Finset K)
    (fr : Σ _xy : (Σ _x : FieldTriple K, FieldTriple K), FieldTriple K) : Finset (FieldTriple K) := by
  classical
  exact A.filter fun v =>
    (((sampledBasisCoordinateEquiv K (frameBasis K A fr)).trans (fieldTripleEquivPi K)) v) 0 ∉ D

/-- A member of the counted fourth-vector fiber has a generating first
coordinate in the selected frame basis. -/
theorem goodFourthFinset_first_coordinate_not_nonGenerator
    (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    [Algebra BinaryField K] [FiniteDimensional BinaryField K] [Finite K]
    (A : Finset (FieldTriple K))
    (fr : Σ _xy : (Σ _x : FieldTriple K, FieldTriple K), FieldTriple K)
    (v : FieldTriple K)
    (hv : v ∈ goodFourthFinset K A (nonGenerators K) fr) :
    (sampledBasisCoordinateEquiv K (canonicalGoodFrameBasis K A fr) v).1 ∉
      nonGenerators K := by
  have h := (Finset.mem_filter.mp hv).2
  simpa [goodFourthFinset, canonicalGoodFrameBasis, fieldTripleEquivPi, frameBasis]
    using h

/-- Canonical Finset count for four actual clean vector draws: the first three
form a sampled K-basis, and the first coordinate of the fourth vector in that
basis avoids the forbidden set D. -/
theorem card_canonical_good_four_tuple_finset_lower
    (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (A : Finset (FieldTriple K)) (D : Finset K) :
    (A.card - D.card * Fintype.card K ^ 2) *
        ((A.card - Fintype.card K ^ 2) *
          ((A.card - Fintype.card K) * (A.card - 1))) ≤
      ((cleanFrameSet (K := K) A).sigma (goodFourthFinset K A D)).card := by
  classical
  let Frames := cleanFrameSet (K := K) A
  let Good := goodFourthFinset K A D
  let m := A.card - D.card * Fintype.card K ^ 2
  have hbase :
      (A.card - Fintype.card K ^ 2) * ((A.card - Fintype.card K) * (A.card - 1)) ≤
        Frames.card := card_clean_frame_finset_lower K A
  have hfiber : ∀ fr ∈ Frames, m ≤ (Good fr).card := by
    intro fr hfr
    let b := frameBasis K A fr
    have hbad := sampled_basis_bad_coordinate_count K A D b
    have hsplit := Finset.card_filter_add_card_filter_not (s := A)
      (fun v : FieldTriple K =>
        (((sampledBasisCoordinateEquiv K b).trans (fieldTripleEquivPi K)) v) 0 ∈ D)
    have hgood' : A.card ≤ D.card * Fintype.card K ^ 2 +
        (A.filter fun v : FieldTriple K =>
          (((sampledBasisCoordinateEquiv K b).trans (fieldTripleEquivPi K)) v) 0 ∉ D).card := by
      omega
    have hgood : A.card - D.card * Fintype.card K ^ 2 ≤
        (A.filter fun v : FieldTriple K =>
          (((sampledBasisCoordinateEquiv K b).trans (fieldTripleEquivPi K)) v) 0 ∉ D).card := by
      apply Nat.sub_le_iff_le_add.mpr
      simpa [Nat.add_comm] using hgood'
    simpa [Good, goodFourthFinset, b, frameBasis, hfr, m] using hgood
  have hsum := card_sigma_finset_lower Frames Good m hfiber
  have hmul := Nat.mul_le_mul_left m hbase
  simpa [Frames, Good, m, Nat.mul_assoc] using hmul.trans hsum

end

end CorruptedFieldRecovery
