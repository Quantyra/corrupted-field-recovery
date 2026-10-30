import CorruptedFieldRecovery.S010ModeImageFrameBridge
import CorruptedFieldRecovery.BinaryFieldTransport
import Mathlib.Tactic

namespace CorruptedFieldRecovery

noncomputable section

/-- Transport an already established sampled four-contraction identification
back to the original physical input. The coordinate equivalence `ι` remains an
explicit supplied input, and the proof follows the conjugation of endomorphisms
rather than identifying it with the separately supplied tape map Q. -/
theorem hidden_four_identification_of_sampled
    (K : Type*) [Field K] [Finite K]
    [Algebra (ZMod (ringChar K)) K]
    {n : Nat}
    (ι : BinaryInput K n ≃ₗ[ZMod (ringChar K)] FieldTriple K)
    (basis : Module.Basis (Fin 3) K (FieldTriple K))
    (v : FieldTriple K) (c : K)
    (hsampled :
      (∀ T : Module.End (ZMod (ringChar K)) (FieldTriple K),
        sampledFourBalanced K c basis v T ↔ T ∈ scalarTripleEndRange K) ∧
      Module.finrank (ZMod (ringChar K)) (scalarTripleEndRange K) =
        Module.finrank (ZMod (ringChar K)) K) :
    (∀ T : Module.End (ZMod (ringChar K)) (BinaryInput K n),
      hiddenFourBalanced K ι basis v c T ↔
        ∃ k : K, ∀ x, T x = ι.symm (k • ι x)) ∧
      Module.finrank (ZMod (ringChar K)) (scalarTripleEndRange K) =
        Module.finrank (ZMod (ringChar K)) K := by
  constructor
  · intro T
    rw [hidden_four_balanced_iff_conjugate K ι basis v c T]
    let q := ι.restrictScalars (ZMod (ringChar K))
    let T' := q.conj T
    rw [hsampled.1 T']
    rw [scalarTripleEndRange_mem_iff]
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      intro x
      apply q.injective
      have hx := hk (q x)
      simpa [T', q, LinearEquiv.conj_apply_apply,
        fieldScalarTriple_eq_smul] using hx
    · rintro ⟨k, hk⟩
      refine ⟨k, ?_⟩
      intro y
      have hy := congrArg q (hk (q.symm y))
      simpa [T', q, LinearEquiv.conj_apply_apply,
        fieldScalarTriple_eq_smul] using hy
  · exact hsampled.2

/-- An actual good five-word tape supplies the clean first-four frame and
sampled four-contraction identification. Under the separately supplied
physical input equivalence `ι`, the same event yields the full physical
balance-if-and-only-if-scalar statement. -/
theorem modeImage_actual_good_tape_hidden_four_identification
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Finite K]
    [CharP K 2] [Algebra BinaryField K] [FiniteDimensional BinaryField K]
    [Algebra (ZMod (ringChar K)) K]
    {s : Nat}
    (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K)
    (E : BinaryTensor (3 * s))
    (U : Submodule BinaryField (KTriple K))
    (b : (Fin 4 → FieldTriple K) → Module.Basis (Fin s) BinaryField K)
    (tape : FiveWordTape s)
    (htape : tape ∈ actualFiveGoodTapeSet K Q
      (modeImageSemanticCleanFieldSet Q E) U b)
    (ι : BinaryInput K (3 * s) ≃ₗ[ZMod (ringChar K)] FieldTriple K)
    (c : K) (hc : c ≠ 0) :
    ∃ fr : Σ _xy : (Σ _x : FieldTriple K, FieldTriple K), FieldTriple K,
      ∃ v : FieldTriple K,
        fr ∈ cleanFrameSet (K := K) (modeImageSemanticCleanFieldSet Q E) ∧
        v ∈ goodFourthFinset K (modeImageSemanticCleanFieldSet Q E)
          (nonGenerators K) fr ∧
        (fun i => Q (tape.1 i)) = canonicalGoodFourFlatTuple K ⟨fr, v⟩ ∧
        ((∀ T : Module.End (ZMod (ringChar K)) (BinaryInput K (3 * s)),
          hiddenFourBalanced K ι
            (canonicalGoodFrameBasis K (modeImageSemanticCleanFieldSet Q E) fr)
            v c T ↔ ∃ k : K, ∀ x, T x = ι.symm (k • ι x)) ∧
          Module.finrank (ZMod (ringChar K)) (scalarTripleEndRange K) =
            Module.finrank (ZMod (ringChar K)) K) := by
  rcases modeImage_actual_good_tape_four_contraction_identification
      Q E U b tape htape c hc with
    ⟨fr, v, hfr, hv, hflat, hsampled⟩
  refine ⟨fr, v, hfr, hv, hflat, ?_⟩
  exact hidden_four_identification_of_sampled K ι
    (canonicalGoodFrameBasis K (modeImageSemanticCleanFieldSet Q E) fr)
    v c hsampled

end

end CorruptedFieldRecovery
