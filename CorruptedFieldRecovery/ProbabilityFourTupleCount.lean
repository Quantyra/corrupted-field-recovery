import CorruptedFieldRecovery.ProbabilityAssembly
import CorruptedFieldRecovery.ProbabilityBasisTransport
import CorruptedFieldRecovery.ProperSubfieldCounts
import Mathlib.Tactic

/-! Combine the first-three sequential K-span count with the actual
basis-relative fourth-vector coordinate-fiber bound. The clean set remains an
arbitrary binary subspace image; no K-linearity is assumed. -/

namespace CorruptedFieldRecovery

open Module

noncomputable section

theorem fieldTriple_finrank (K : Type*) [Field K] :
    finrank K (FieldTriple K) = 3 := by
  simp [FieldTriple, Module.finrank_prod]

def GoodFourthCoordinate
    (K : Type*) [Field K] [Fintype K] [DecidableEq (FieldTriple K)]
    (A : Finset (FieldTriple K)) (D : Finset K)
    (t : CleanBasisTriple (K := K) A) :=
  {x : FieldTriple K // x ∈ A ∧
    (((sampledBasisCoordinateEquiv K
      (cleanBasisTripleBasis t (fieldTriple_finrank K))).trans
        (fieldTripleEquivPi K)) x) 0 ∉ D}

theorem card_good_fourth_coordinate_lower
    (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (A : Finset (FieldTriple K)) (D : Finset K)
    (t : CleanBasisTriple (K := K) A) :
    A.card - D.card * Fintype.card K ^ 2 ≤
      Fintype.card (GoodFourthCoordinate K A D t) := by
  classical
  let b := cleanBasisTripleBasis t (fieldTriple_finrank K)
  let coord := (sampledBasisCoordinateEquiv K b).trans (fieldTripleEquivPi K)
  let p : FieldTriple K → Prop := fun x => (coord x) 0 ∈ D
  letI : DecidablePred p := Classical.decPred p
  letI : DecidablePred (fun x => ¬ p x) := Classical.decPred _
  have hsplit := Finset.card_filter_add_card_filter_not (s := A) p
  have hgoodcard : Fintype.card {x : FieldTriple K // x ∈ A ∧ ¬ p x} =
      (A.filter fun x => ¬ p x).card := by
    apply Fintype.card_of_subtype (s := A.filter fun x => ¬ p x)
    intro x
    simp [Finset.mem_filter]
  have hbad : (A.filter p).card ≤ D.card * Fintype.card K ^ 2 := by
    change (A.filter fun x => (coord x) 0 ∈ D).card ≤
      D.card * Fintype.card K ^ 2
    exact sampled_basis_bad_coordinate_count K A D b
  change A.card - D.card * Fintype.card K ^ 2 ≤
    Fintype.card {x : FieldTriple K // x ∈ A ∧ ¬ p x}
  rw [hgoodcard]
  omega

private theorem card_sigma_fiber_lower
    {I : Type*} [Fintype I] {F : I → Type*} [∀ i, Fintype (F i)]
    (m : ℕ) (h : ∀ i, m ≤ Fintype.card (F i)) :
    m * Fintype.card I ≤ Fintype.card (Σ i, F i) := by
  classical
  rw [Fintype.card_sigma]
  calc
    m * Fintype.card I = ∑ _i : I, m := by simp [Nat.mul_comm]
    _ ≤ ∑ i : I, Fintype.card (F i) := Finset.sum_le_sum fun i _ => h i

/-- Concrete lower bound for four clean physical draws satisfying both the
first-three K-basis event and the fourth-vector, sampled-basis coordinate
generator event. `D` is the forbidden coordinate set; taking `D` to be the
proper-subfield nongenerators instantiates the field-generation part of S010. -/
theorem card_four_clean_basis_generator_tuples_lower
    (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (A : Finset (FieldTriple K)) (D : Finset K) :
    (A.card - D.card * Fintype.card K ^ 2) *
        ((A.card - Fintype.card K ^ 2) *
          ((A.card - Fintype.card K) * (A.card - 1))) ≤
      Fintype.card (Σ t : CleanBasisTriple (K := K) A, GoodFourthCoordinate K A D t) := by
  classical
  let Triple := CleanBasisTriple (K := K) A
  let GoodFourth := GoodFourthCoordinate K A D
  let m := A.card - D.card * Fintype.card K ^ 2
  have hbase :
      (A.card - Fintype.card K ^ 2) *
        ((A.card - Fintype.card K) * (A.card - 1)) ≤ Fintype.card Triple :=
    card_clean_basis_triples_lower (K := K) (V := FieldTriple K) A
  have hfiber : ∀ t : Triple, m ≤ Fintype.card (GoodFourth t) := by
    intro t
    exact card_good_fourth_coordinate_lower K A D t
  have hsum := card_sigma_fiber_lower m hfiber
  have hmul := Nat.mul_le_mul_left m hbase
  simpa [Triple, GoodFourth, m, Nat.mul_assoc] using hmul.trans hsum

end

end CorruptedFieldRecovery
