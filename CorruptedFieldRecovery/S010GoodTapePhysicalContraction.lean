import CorruptedFieldRecovery.S010ModeImageFrameBridge
import CorruptedFieldRecovery.S010PhysicalPerturbedContraction
import CorruptedFieldRecovery.S010ModeImageFiveCount
import Mathlib.Tactic

namespace CorruptedFieldRecovery

noncomputable section

/-- Every one of the four physical words in an actual good tape belongs to the
annihilator of the actual mode image of the hidden tensor. The proof uses the
accepted semantic clean-set correspondence and the actual first-four frame
witness extracted from the tape event. -/
theorem modeImage_actual_good_tape_words_clean
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Finite K]
    [Algebra BinaryField K] [FiniteDimensional BinaryField K]
    [CharP K 2] [Algebra (ZMod (ringChar K)) K]
    {s : Nat}
    (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K)
    (E : BinaryTensor (3 * s))
    (U : Submodule BinaryField (KTriple K))
    (b : (Fin 4 → FieldTriple K) → Module.Basis (Fin s) BinaryField K)
    (tape : FiveWordTape s)
    (htape : tape ∈ actualFiveGoodTapeSet K Q
      (modeImageSemanticCleanFieldSet Q E) U b) :
    ∀ i : Fin 4, tape.1 i ∈ (modeImage E).dualCoannihilator := by
  classical
  rcases modeImage_actual_good_tape_four_contraction_identification
      Q E U b tape htape (1 : K) one_ne_zero with
    ⟨fr, v, hfr, hv, hflat, _⟩
  let A := modeImageSemanticCleanFieldSet Q E
  have hframeParts := Finset.mem_sigma.mp hfr
  have hframePair := hframeParts.1
  change fr.1 ∈
      (A.filter fun x : FieldTriple K => x ≠ 0).sigma (fun x =>
        A.filter fun y => y ∉ Submodule.span K
          (({x} : Finset (FieldTriple K)) : Set (FieldTriple K)))
    at hframePair
  have hpairParts := Finset.mem_sigma.mp hframePair
  have hfirst : fr.1.1 ∈ A := (Finset.mem_filter.mp hpairParts.1).1
  have hsecond : fr.1.2 ∈ A := (Finset.mem_filter.mp hpairParts.2).1
  have hthird : fr.2 ∈ A := (Finset.mem_filter.mp hframeParts.2).1
  have hfourth : v ∈ A := (Finset.mem_filter.mp hv).1
  have hflatA : ∀ i : Fin 4, canonicalGoodFourFlatTuple K ⟨fr, v⟩ i ∈ A := by
    intro i
    fin_cases i
    · simpa [canonicalGoodFourFlatTuple] using hfirst
    · simpa [canonicalGoodFourFlatTuple] using hsecond
    · simpa [canonicalGoodFourFlatTuple] using hthird
    · simpa [canonicalGoodFourFlatTuple] using hfourth
  intro i
  apply (modeImage_physical_clean_iff Q E (tape.1 i)).2
  have hA : Q (tape.1 i) ∈ A := by
    rw [congrFun hflat i]
    exact hflatA i
  simpa [A] using hA

/-- On each triple of the first four words of an actual good tape, the hidden
part of the manuscript's physical perturbed tensor C + E vanishes in the
third-slot contraction. Thus the measured contraction agrees exactly with the
compatible tensor C. -/
theorem modeImage_actual_good_tape_perturbed_contraction_eq_clean
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Finite K]
    [Algebra BinaryField K] [FiniteDimensional BinaryField K]
    [CharP K 2] [Algebra (ZMod (ringChar K)) K]
    {s : Nat}
    (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K)
    (E C : BinaryTensor (3 * s))
    (U : Submodule BinaryField (KTriple K))
    (b : (Fin 4 → FieldTriple K) → Module.Basis (Fin s) BinaryField K)
    (tape : FiveWordTape s)
    (htape : tape ∈ actualFiveGoodTapeSet K Q
      (modeImageSemanticCleanFieldSet Q E) U b)
    (i j k : Fin 4) :
    physicalBinaryContraction (physicalPerturbedTensor C E LinearMap.id)
      (tape.1 i) (tape.1 j) (tape.1 k) = C (tape.1 i) (tape.1 j) (tape.1 k) := by
  apply physicalPerturbedContraction_eq_clean_on_modeImage_coannihilator
  exact modeImage_actual_good_tape_words_clean Q E U b tape htape k

end

end CorruptedFieldRecovery
