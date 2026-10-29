import CorruptedFieldRecovery.ProbabilityCanonicalFourTuples
import CorruptedFieldRecovery.ProperSubfieldCounts
import Mathlib.Tactic

/-! A flat physical-tuple image of the canonical Finset event. The map forgets
only the nested grouping of the first three values; injectivity shows that its
cardinality is the actual number of distinct four-draw tuples. -/

namespace CorruptedFieldRecovery

noncomputable section

def canonicalGoodFourFlatTuple
    (K : Type*)
    (x : Σ _fr : (Σ _xy : (Σ _x : FieldTriple K, FieldTriple K), FieldTriple K),
        FieldTriple K) : Fin 4 → FieldTriple K :=
  Fin.cons x.1.1.1
    (Fin.cons x.1.1.2
      (Fin.cons x.1.2 (fun _ : Fin 1 => x.2)))

theorem canonicalGoodFourFlatTuple_injective
    (K : Type*) : Function.Injective (canonicalGoodFourFlatTuple K) := by
  intro x y h
  rcases x with ⟨⟨⟨x₀, x₁⟩, x₂⟩, x₃⟩
  rcases y with ⟨⟨⟨y₀, y₁⟩, y₂⟩, y₃⟩
  have h₀ : x₀ = y₀ := by
    have h' := congrFun h 0
    simpa [canonicalGoodFourFlatTuple] using h'
  have h₁ : x₁ = y₁ := by
    have h' := congrFun h 1
    simpa [canonicalGoodFourFlatTuple] using h'
  have h₂ : x₂ = y₂ := by
    have h' := congrFun h 2
    simpa [canonicalGoodFourFlatTuple] using h'
  have h₃ : x₃ = y₃ := by
    have h' := congrFun h 3
    simpa [canonicalGoodFourFlatTuple] using h'
  subst y₀
  subst y₁
  subst y₂
  subst y₃
  rfl

def canonicalGoodFourFlatImage
    (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (A : Finset (FieldTriple K)) (D : Finset K) :
    Finset (Fin 4 → FieldTriple K) :=
  (cleanFrameSet (K := K) A).sigma (goodFourthFinset K A D) |>.map
    ⟨canonicalGoodFourFlatTuple K,
      canonicalGoodFourFlatTuple_injective K⟩

theorem mem_canonicalGoodFourFlatImage_iff
    (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (A : Finset (FieldTriple K)) (D : Finset K)
    (x : Fin 4 → FieldTriple K) :
    x ∈ canonicalGoodFourFlatImage K A D ↔
      ∃ fr ∈ cleanFrameSet (K := K) A,
        ∃ v ∈ goodFourthFinset K A D fr,
          canonicalGoodFourFlatTuple K ⟨fr, v⟩ = x := by
  simp only [canonicalGoodFourFlatImage, Finset.mem_map]
  constructor
  · rintro ⟨y, hy, hxy⟩
    rcases Finset.mem_sigma.mp hy with ⟨hyfr, hyv⟩
    exact ⟨y.1, hyfr, y.2, hyv, hxy⟩
  · rintro ⟨fr, hfr, v, hv, hxy⟩
    exact ⟨⟨fr, v⟩, Finset.mem_sigma.mpr ⟨hfr, hv⟩, hxy⟩

/-- The canonical nested sigma and its flat image count the same distinct
four-draw tuples. Every image member has a basis triple and a fourth clean
vector whose sampled-basis first coordinate is outside D. -/
theorem card_canonicalGoodFourFlatImage_lower
    (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (A : Finset (FieldTriple K)) (D : Finset K) :
    (A.card - D.card * Fintype.card K ^ 2) *
        ((A.card - Fintype.card K ^ 2) *
          ((A.card - Fintype.card K) * (A.card - 1))) ≤
      (canonicalGoodFourFlatImage K A D).card := by
  rw [canonicalGoodFourFlatImage, Finset.card_map]
  exact card_canonical_good_four_tuple_finset_lower K A D

/-- Specialization to the actual fourth-coordinate generator event: D is the
set of elements that do not generate K over its binary prime field. -/
theorem card_canonicalGoodFourGeneratorFlatImage_lower
    (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    [Algebra BinaryField K] [FiniteDimensional BinaryField K] [Finite K]
    (A : Finset (FieldTriple K)) :
    (A.card - (nonGenerators K).card * Fintype.card K ^ 2) *
        ((A.card - Fintype.card K ^ 2) *
          ((A.card - Fintype.card K) * (A.card - 1))) ≤
      (canonicalGoodFourFlatImage K A (nonGenerators K)).card :=
  card_canonicalGoodFourFlatImage_lower K A (nonGenerators K)

end

end CorruptedFieldRecovery
