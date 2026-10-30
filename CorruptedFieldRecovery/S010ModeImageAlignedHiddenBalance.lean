import CorruptedFieldRecovery.S010GoodTapeHiddenBalance
import CorruptedFieldRecovery.S010QInputEquivalence
import Mathlib.Tactic

namespace CorruptedFieldRecovery

noncomputable section

/-- The coordinatewise transport of the physical input's coefficient ring to
`ZMod 2`, using the derived characteristic-two equality. -/
def modeImage_inputVectorToBinary
    {K : Type*} [Field K] [CharP K 2] {n : Nat} :
    BinaryInput K n ≃ BinaryVector n :=
  Equiv.cast (congrArg (fun p => Fin n → ZMod p) (ringChar.eq K 2))

/-- Final Q-aligned form of the actual good-tape four-contraction result.
The physical input equivalence is derived from Q and `ringChar K = 2`, and
its pointwise agreement with Q is included in the conclusion. -/
theorem modeImage_actual_good_tape_hidden_balance_from_Q
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
    (c : K) (hc : c ≠ 0) :
    ∃ fr : Σ _xy : (Σ _x : FieldTriple K, FieldTriple K), FieldTriple K,
      ∃ v : FieldTriple K,
        fr ∈ cleanFrameSet (K := K) (modeImageSemanticCleanFieldSet Q E) ∧
        v ∈ goodFourthFinset K (modeImageSemanticCleanFieldSet Q E)
          (nonGenerators K) fr ∧
        (fun i => Q (tape.1 i)) = canonicalGoodFourFlatTuple K ⟨fr, v⟩ ∧
        (∀ x : BinaryInput K (3 * s),
          modeImage_inputEquiv_from_Q Q x =
            Q (modeImage_inputVectorToBinary (K := K) x)) ∧
        ((∀ T : Module.End (ZMod (ringChar K)) (BinaryInput K (3 * s)),
          hiddenFourBalanced K (modeImage_inputEquiv_from_Q Q)
            (canonicalGoodFrameBasis K (modeImageSemanticCleanFieldSet Q E) fr)
            v c T ↔
              ∃ k : K, ∀ x,
                T x = (modeImage_inputEquiv_from_Q Q).symm (k •
                  modeImage_inputEquiv_from_Q Q x)) ∧
          Module.finrank (ZMod (ringChar K)) (scalarTripleEndRange K) =
            Module.finrank (ZMod (ringChar K)) K) := by
  rcases modeImage_actual_good_tape_hidden_four_identification
      Q E U b tape htape (modeImage_inputEquiv_from_Q Q) c hc with
    ⟨fr, v, hfr, hv, hflat, hhidden⟩
  refine ⟨fr, v, hfr, hv, hflat, ?_, hhidden⟩
  intro x
  simpa [modeImage_inputVectorToBinary] using
    modeImage_inputEquiv_from_Q_apply Q x

end

end CorruptedFieldRecovery
