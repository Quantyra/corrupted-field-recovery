import CorruptedFieldRecovery.S010ConditionalAmplification
import CorruptedFieldRecovery.ProbabilityCanonicalFlatTupleBridge
import CorruptedFieldRecovery.BinaryFieldTransport
import Mathlib.Tactic

namespace CorruptedFieldRecovery

open Module

noncomputable section

private theorem zmod_adjoin_top_transport
    {p : Nat} (K : Type*) [Field K]
    (algP : Algebra (ZMod p) K) (alg2 : Algebra (ZMod 2) K)
    (a : K) (hp : p = 2)
    (h : @Algebra.adjoin (ZMod 2) K _ _ alg2 ({a} : Set K) = ⊤) :
    @Algebra.adjoin (ZMod p) K _ _ algP ({a} : Set K) = ⊤ := by
  subst p
  have hAlg : algP = alg2 := Subsingleton.elim _ _
  cases hAlg
  exact h

/-- The good fourth-vector fiber, built from an actual clean first-three
frame, supplies the generating coordinate needed by the sampled four-
contraction identification theorem. -/
theorem canonicalGoodFrame_fourth_identification
    (K : Type*) [Field K] [Fintype K] [DecidableEq K] [Finite K]
    [CharP K 2] [Algebra BinaryField K] [FiniteDimensional BinaryField K]
    [Algebra (ZMod (ringChar K)) K]
    (A : Finset (FieldTriple K))
    (fr : Σ _xy : (Σ _x : FieldTriple K, FieldTriple K), FieldTriple K)
    (hfr : fr ∈ cleanFrameSet (K := K) A)
    (v : FieldTriple K)
    (hv : v ∈ goodFourthFinset K A (nonGenerators K) fr)
    (c : K) (hc : c ≠ 0) :
    (∀ T : Module.End (ZMod (ringChar K)) (FieldTriple K),
      sampledFourBalanced K c (canonicalGoodFrameBasis K A fr) v T ↔
        T ∈ scalarTripleEndRange K) ∧
      Module.finrank (ZMod (ringChar K)) (scalarTripleEndRange K) =
        Module.finrank (ZMod (ringChar K)) K := by
  let B := canonicalGoodFrameBasis K A fr
  have hframe := canonicalGoodFrameBasis_eq_cleanBasisTripleBasis K A fr hfr
  have hnot : (sampledBasisCoordinateEquiv K B v).1 ∉ nonGenerators K := by
    simpa [B, hframe] using
      (goodFourthFinset_first_coordinate_not_nonGenerator K A fr v hv)
  have hgenBinary :
      Algebra.adjoin BinaryField
        ({(sampledBasisCoordinateEquiv K B v).1} : Set K) = ⊤ := by
    by_contra hbad
    have hmem : (sampledBasisCoordinateEquiv K B v).1 ∈ nonGenerators K := by
      simp [nonGenerators, hbad]
    exact hnot hmem
  have hchar : ringChar K = 2 := ringChar.eq K 2
  have hgen : Algebra.adjoin (ZMod (ringChar K))
      { (sampledBasisCoordinateEquiv K B v).1 } = ⊤ := by
    exact zmod_adjoin_top_transport K
      (inferInstance : Algebra (ZMod (ringChar K)) K)
      (inferInstance : Algebra (ZMod 2) K)
      (sampledBasisCoordinateEquiv K B v).1 hchar hgenBinary
  exact (sampled_four_contractions_identification_and_finrank
    K B v c hc (Or.inl hgen))

/-- Every member of the actual good five-word tape event has a sampled
first-three field basis and a fourth vector whose generator coordinate
triggers the actual sampled four-contraction identification. The fifth-word
fiber remains governed by its supplied deterministic basis family `b`. -/
theorem modeImage_actual_good_tape_four_contraction_identification
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Finite K]
    [CharP K 2] [Algebra BinaryField K] [FiniteDimensional BinaryField K]
    [Algebra (ZMod (ringChar K)) K]
    {s : Nat} (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K)
    (E : BinaryTensor (3 * s))
    (U : Submodule BinaryField (KTriple K))
    (b : (Fin 4 → FieldTriple K) → Module.Basis (Fin s) BinaryField K)
    (tape : FiveWordTape s)
    (htape : tape ∈ actualFiveGoodTapeSet K Q
      (modeImageSemanticCleanFieldSet Q E) U b)
    (c : K) (hc : c ≠ 0) :
    ∃ fr : Σ _xy : (Σ _x : FieldTriple K, FieldTriple K), FieldTriple K,
      ∃ v : FieldTriple K,
        fr ∈ cleanFrameSet (K := K) (modeImageSemanticCleanFieldSet Q E) ∧
        v ∈ goodFourthFinset K (modeImageSemanticCleanFieldSet Q E)
          (nonGenerators K) fr ∧
        (fun i => Q (tape.1 i)) = canonicalGoodFourFlatTuple K ⟨fr, v⟩ ∧
        ((∀ T : Module.End (ZMod (ringChar K)) (FieldTriple K),
          sampledFourBalanced K c
            (canonicalGoodFrameBasis K (modeImageSemanticCleanFieldSet Q E) fr)
            v T ↔ T ∈ scalarTripleEndRange K) ∧
          Module.finrank (ZMod (ringChar K)) (scalarTripleEndRange K) =
            Module.finrank (ZMod (ringChar K)) K) := by
  classical
  rcases Finset.mem_map.mp htape with ⟨z, hz, hzTape⟩
  rcases z with ⟨words, index⟩
  have hwords : (fun i => Q (tape.1 i)) = words := by
    have hphysical : tape.1 = fun i => Q.symm (words i) := by
      have hp := congrArg Prod.fst hzTape.symm
      simpa [fiveTapeSemanticEquiv] using hp
    funext i
    rw [hphysical]
    exact Q.apply_symm_apply (words i)
  have hz' : (⟨words, index⟩ : Σ _e : Fin 4 → FieldTriple K, BinaryVector s) ∈
      goodFiveTupleSigma K (modeImageSemanticCleanFieldSet Q E) U b := by
    simpa [actualFiveGoodTapeSet, fiveTapeSemanticEquiv] using hz
  have hparts := Finset.mem_sigma.mp hz'
  obtain ⟨fr, hfr, v, hv, hflat⟩ :=
    (mem_canonicalGoodFourFlatImage_iff K
      (modeImageSemanticCleanFieldSet Q E) (nonGenerators K) words).mp hparts.1
  have hident := canonicalGoodFrame_fourth_identification K
    (modeImageSemanticCleanFieldSet Q E) fr hfr v hv c hc
  refine ⟨fr, v, hfr, hv, ?_, hident⟩
  exact hwords.trans hflat.symm

end

end CorruptedFieldRecovery
