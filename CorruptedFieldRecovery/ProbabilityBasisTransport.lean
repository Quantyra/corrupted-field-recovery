import CorruptedFieldRecovery.FourContractions
import CorruptedFieldRecovery.ConditionalCounts
import Mathlib.Tactic

/-! Transport the arbitrary-clean-set fiber bound through the sampled basis
coordinate equivalence. This is the fourth-vector generator event used by the
trial: the coordinate is relative to the actual first-three sampled basis. -/

namespace CorruptedFieldRecovery

open Module

noncomputable section

/-- For a fixed sampled K-basis, the number of clean fourth vectors whose
first basis coordinate lies in a specified bad set is bounded by the ambient
fiber count. The proof transports the clean set through the basis equivalence;
it does not require the clean set to be K-linear. -/
theorem sampled_basis_bad_coordinate_count
    (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (A : Finset (FieldTriple K)) (D : Finset K)
    (b : Basis (Fin 3) K (FieldTriple K)) :
    (A.filter fun x =>
      ((sampledBasisCoordinateEquiv K b).trans (fieldTripleEquivPi K) x) 0 ∈ D).card ≤
      D.card * Fintype.card K ^ 2 := by
  classical
  let e := (sampledBasisCoordinateEquiv K b).trans (fieldTripleEquivPi K)
  let Acoord : Finset (Fin 3 → K) := A.map e.toEquiv.toEmbedding
  let S : Finset (FieldTriple K) :=
    A.filter fun x => (e x) 0 ∈ D
  let T : Finset (Fin 3 → K) := Acoord.filter fun y => y 0 ∈ D
  have hcard : S.card ≤ T.card := by
    let f : {x // x ∈ S} → {y // y ∈ T} := fun x =>
      ⟨e x.1, by
        simp only [T, Finset.mem_filter]
        refine ⟨?_, (Finset.mem_filter.mp x.2).2⟩
        exact Finset.mem_map.mpr ⟨x.1, (Finset.mem_filter.mp x.2).1, rfl⟩⟩
    have hfinj : Function.Injective f := by
      intro x y h
      apply Subtype.ext
      exact e.injective (congrArg Subtype.val h)
    have hc := Fintype.card_le_of_injective f hfinj
    simpa [Fintype.card_coe] using hc
  have hfiber := card_subset_first_coordinate_values_le K Acoord D
  dsimp [S, T] at hcard ⊢
  exact hcard.trans hfiber

end

end CorruptedFieldRecovery
