import CorruptedFieldRecovery.ProbabilityCanonicalFlatTupleBridge
import CorruptedFieldRecovery.TranslateScalarCounts
import CorruptedFieldRecovery.ProperSubfieldCounts
import CorruptedFieldRecovery.BinaryTensor
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Tactic

/-! Concrete finite count for the four-word event and its independent fifth
`s`-bit index. The index-to-field map may depend on the sampled four-tuple:
it is supplied by a deterministically selected ordered binary basis. -/

namespace CorruptedFieldRecovery

open Module

noncomputable section

variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]
  [Algebra BinaryField K] [FiniteDimensional BinaryField K] [Finite K]

/-- Convert binary coordinates to the field using the supplied ordered basis.
The inverse basis coordinate map is an equivalence, so this works for every
deterministic choice of basis, including a choice depending on earlier words. -/
def basisFifthIndexEquiv {s : Nat}
    (b : Basis (Fin s) BinaryField K) : BinaryVector s ≃ K :=
  (b.equivFun).toEquiv.symm

/-- Fifth scalar values which generate the field and avoid every bad translate. -/
def goodFifthScalars (U : Submodule BinaryField (KTriple K)) : Finset K :=
  Finset.univ \ (nonGenerators K ∪
    badTranslateScalars K (supportCoordinateFinset K U))

/-- Pull the good scalar set back to the independent `s`-bit fifth index. -/
def goodFifthIndices {s : Nat} (b : Basis (Fin s) BinaryField K)
    (U : Submodule BinaryField (KTriple K)) : Finset (BinaryVector s) :=
  (goodFifthScalars K U).map
    ⟨(basisFifthIndexEquiv K b).symm, (basisFifthIndexEquiv K b).symm.injective⟩

/-- The dependent five-event set. Each qualifying flat four-word tuple has
its own basis and its own good fifth-index fiber. -/
def goodFiveTupleSigma {s : Nat} (A : Finset (FieldTriple K))
    (U : Submodule BinaryField (KTriple K))
    (b : (Fin 4 → FieldTriple K) → Basis (Fin s) BinaryField K) :
    Finset (Σ _e : Fin 4 → FieldTriple K, BinaryVector s) :=
  (canonicalGoodFourFlatImage K A (nonGenerators K)).sigma
    (fun e => goodFifthIndices K (b e) U)

private theorem card_sigma_finset
    {I : Type*} {J : I → Type*} (S : Finset I)
    (F : ∀ i, Finset (J i)) :
    (S.sigma F).card = ∑ i ∈ S, (F i).card := by
  simp [Finset.sigma, Multiset.card_sigma]

/-- The actual flat four-word generator count and the actual bad-scalar
finite-set counts give a concrete five-word lower count. The fifth basis may
depend on the preceding four words; each equivalence preserves the same fiber
cardinality. No probability bound or independence hypothesis is assumed. -/
theorem card_goodFiveTupleSigma_lower {s : Nat}
    (A : Finset (FieldTriple K)) (U : Submodule BinaryField (KTriple K))
    (b : (Fin 4 → FieldTriple K) → Basis (Fin s) BinaryField K)
    (r : Nat) (hr : Module.finrank BinaryField U = r) :
    ((A.card - (nonGenerators K).card * Fintype.card K ^ 2) *
      ((A.card - Fintype.card K ^ 2) *
        ((A.card - Fintype.card K) * (A.card - 1)))) *
      (Fintype.card K -
        ((∑ d ∈ properDegrees K, 2 ^ d) + (2 ^ (2 * r) - 1))) ≤
      (goodFiveTupleSigma K A U b).card := by
  classical
  let E := canonicalGoodFourFlatImage K A (nonGenerators K)
  let G := goodFifthScalars K U
  have hfour := card_canonicalGoodFourGeneratorFlatImage_lower K A
  have hgen := card_nonGenerators_le_proper_degree_sum K
  have htrans := card_badTranslateScalars_submodule_le K U
  have hbad : (nonGenerators K ∪
      badTranslateScalars K (supportCoordinateFinset K U)).card ≤
      (∑ d ∈ properDegrees K, 2 ^ d) + (2 ^ (2 * r) - 1) := by
    calc
      _ ≤ (nonGenerators K).card +
          (badTranslateScalars K (supportCoordinateFinset K U)).card :=
        Finset.card_union_le _ _
      _ ≤ (∑ d ∈ properDegrees K, 2 ^ d) + (2 ^ (2 * r) - 1) := by
        have htrans' :
            (badTranslateScalars K (supportCoordinateFinset K U)).card ≤
              2 ^ (2 * r) - 1 := by
          simpa [BinaryField, hr] using htrans
        omega
  have hgood : Fintype.card K -
      ((∑ d ∈ properDegrees K, 2 ^ d) + (2 ^ (2 * r) - 1)) ≤ G.card := by
    let B := nonGenerators K ∪
      badTranslateScalars K (supportCoordinateFinset K U)
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset K)) (fun x : K => x ∈ B)
    have hbad' : B.card ≤
        (∑ d ∈ properDegrees K, 2 ^ d) + (2 ^ (2 * r) - 1) := by
      simpa [B] using hbad
    have hG : (Finset.univ.filter fun x : K => x ∉ B) = G := by
      ext x
      simp [G, goodFifthScalars, B]
    have hBset : (Finset.univ.filter fun x : K => x ∈ B) = B := by
      ext x
      simp
    have hB : (Finset.univ.filter fun x : K => x ∈ B).card = B.card :=
      congrArg Finset.card hBset
    rw [hG, hB, Finset.card_univ] at hsplit
    omega
  have hfiber : ∀ e ∈ E,
      Fintype.card K -
        ((∑ d ∈ properDegrees K, 2 ^ d) + (2 ^ (2 * r) - 1)) ≤
      (goodFifthIndices K (b e) U).card := by
    intro e he
    calc
      _ ≤ G.card := hgood
      _ = (goodFifthIndices K (b e) U).card := by
        simp [G, goodFifthIndices, goodFifthScalars, Finset.card_map]
  have hsum :
      (Fintype.card K -
        ((∑ d ∈ properDegrees K, 2 ^ d) + (2 ^ (2 * r) - 1))) * E.card ≤
      ∑ e ∈ E, (goodFifthIndices K (b e) U).card := by
    calc
      _ = ∑ _e ∈ E,
          (Fintype.card K -
            ((∑ d ∈ properDegrees K, 2 ^ d) + (2 ^ (2 * r) - 1))) := by
        simp [Nat.mul_comm]
      _ ≤ ∑ e ∈ E, (goodFifthIndices K (b e) U).card := by
        apply Finset.sum_le_sum
        intro e he
        exact hfiber e he
  have hfour' :
      (A.card - (nonGenerators K).card * Fintype.card K ^ 2) *
        ((A.card - Fintype.card K ^ 2) *
          ((A.card - Fintype.card K) * (A.card - 1))) ≤ E.card := by
    simpa [E] using hfour
  rw [← card_sigma_finset] at hsum
  calc
    _ ≤ E.card * (Fintype.card K -
        ((∑ d ∈ properDegrees K, 2 ^ d) + (2 ^ (2 * r) - 1))) :=
      Nat.mul_le_mul_right _ hfour'
    _ = (Fintype.card K -
        ((∑ d ∈ properDegrees K, 2 ^ d) + (2 ^ (2 * r) - 1))) * E.card :=
      Nat.mul_comm _ _
    _ ≤ (goodFiveTupleSigma K A U b).card := by
      simpa [goodFiveTupleSigma, E] using hsum

end

end CorruptedFieldRecovery
