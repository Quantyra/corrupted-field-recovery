import CorruptedFieldRecovery.ProbabilityFourTupleCount
import Mathlib.Tactic

/-! Embed the nested witness-counted four-word event into the actual flat
four-draw sample space. The injective map forgets only proof witnesses, so its
image is a finset of distinct physical tuples satisfying the certified event. -/

namespace CorruptedFieldRecovery

noncomputable section

def cleanGoodFourFlatTuple
    (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (A : Finset (FieldTriple K)) (D : Finset K)
    (x : Σ t : CleanBasisTriple (K := K) A, GoodFourthCoordinate K A D t) :
    Fin 4 → FieldTriple K :=
  Fin.cons x.1.1.1.1
    (Fin.cons x.1.1.2.1
      (Fin.cons x.1.2.1 (fun _ : Fin 1 => x.2.1)))

theorem cleanGoodFourFlatTuple_injective
    (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (A : Finset (FieldTriple K)) (D : Finset K) :
    Function.Injective (cleanGoodFourFlatTuple K A D) := by
  intro x y h
  rcases x with ⟨⟨⟨⟨x₀, hx₀⟩, ⟨x₁, hx₁⟩⟩, ⟨x₂, hx₂⟩⟩, ⟨x₃, hx₃⟩⟩
  rcases y with ⟨⟨⟨⟨y₀, hy₀⟩, ⟨y₁, hy₁⟩⟩, ⟨y₂, hy₂⟩⟩, ⟨y₃, hy₃⟩⟩
  have h₀ : x₀ = y₀ := by
    have h' := congrFun h 0
    simpa [cleanGoodFourFlatTuple] using h'
  have h₁ : x₁ = y₁ := by
    have h' := congrFun h 1
    simpa [cleanGoodFourFlatTuple] using h'
  have h₂ : x₂ = y₂ := by
    have h' := congrFun h 2
    simpa [cleanGoodFourFlatTuple] using h'
  have h₃ : x₃ = y₃ := by
    have h' := congrFun h 3
    simpa [cleanGoodFourFlatTuple] using h'
  subst y₀
  subst y₁
  subst y₂
  subst y₃
  rfl

/-- The number of distinct flat four-word sample tuples with a witness for the
basis and fourth-coordinate generator event is at least the same finite count
as the nested sigma type. This is the tuple-space bridge needed before division
by the full `q^12` physical sample-space cardinality. -/
theorem card_flat_good_four_tuple_image_lower
    (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (A : Finset (FieldTriple K)) (D : Finset K) :
    (A.card - D.card * Fintype.card K ^ 2) *
        ((A.card - Fintype.card K ^ 2) *
          ((A.card - Fintype.card K) * (A.card - 1))) ≤
      (Finset.univ.map
        ⟨cleanGoodFourFlatTuple K A D,
          cleanGoodFourFlatTuple_injective K A D⟩).card := by
  have hcount := card_four_clean_basis_generator_tuples_lower K A D
  have hcard : Fintype.card
      (Σ t : CleanBasisTriple (K := K) A, GoodFourthCoordinate K A D t) =
      (Finset.univ.map
        ⟨cleanGoodFourFlatTuple K A D,
          cleanGoodFourFlatTuple_injective K A D⟩).card := by
    calc
      Fintype.card (Σ t : CleanBasisTriple (K := K) A,
          GoodFourthCoordinate K A D t) = Finset.univ.card :=
        (Finset.card_univ).symm
      _ = (Finset.univ.map
          ⟨cleanGoodFourFlatTuple K A D,
            cleanGoodFourFlatTuple_injective K A D⟩).card := by
        rw [Finset.card_map]
  rw [← hcard]
  exact hcount

end

end CorruptedFieldRecovery
