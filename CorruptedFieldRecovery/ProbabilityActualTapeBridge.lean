import CorruptedFieldRecovery.ProbabilityFiveTupleAssembly
import CorruptedFieldRecovery.SamplingCounts
import Mathlib.Tactic

/-! Transport the semantic five-event count to the actual independent fair-bit
tape: four physical `3*s`-bit words followed by one `s`-bit index. -/

namespace CorruptedFieldRecovery

open Module

noncomputable section

abbrev FiveWordTape (s : Nat) :=
  (Fin 4 → BinaryVector (3 * s)) × BinaryVector s

/-- The explicit semantic coordinate map on the actual five-word tape. -/
def fiveTapeSemanticEquiv {s : Nat} (K : Type*) [Field K]
    [Algebra BinaryField K]
    (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K) :
    FiveWordTape s ≃ (Σ _e : Fin 4 → FieldTriple K, BinaryVector s) where
  toFun tape := ⟨fun i => Q (tape.1 i), tape.2⟩
  invFun event := (fun i => Q.symm (event.1 i), event.2)
  left_inv := by
    intro tape
    rcases tape with ⟨words, index⟩
    change (fun i => Q.symm (Q (words i)), index) = (words, index)
    apply Prod.ext
    · funext i
      exact Q.symm_apply_apply (words i)
    · rfl
  right_inv := by
    intro event
    rcases event with ⟨words, index⟩
    change (⟨fun i => Q (Q.symm (words i)), index⟩ :
      Σ _e : Fin 4 → FieldTriple K, BinaryVector s) = ⟨words, index⟩
    apply Sigma.ext
    · funext i
      exact Q.apply_symm_apply (words i)
    · rfl

/-- Pull the dependent semantic good-event set back to the physical tape. -/
def actualFiveGoodTapeSet {s : Nat} (K : Type*) [Field K] [Fintype K]
    [DecidableEq K] [Algebra BinaryField K] [FiniteDimensional BinaryField K]
    [Finite K] (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K)
    (A : Finset (FieldTriple K)) (U : Submodule BinaryField (KTriple K))
    (b : (Fin 4 → FieldTriple K) → Basis (Fin s) BinaryField K) :
    Finset (FiveWordTape s) :=
  (goodFiveTupleSigma K A U b).map
    ⟨(fiveTapeSemanticEquiv K Q).symm,
      (fiveTapeSemanticEquiv K Q).symm.injective⟩

theorem card_actualFiveGoodTapeSet {s : Nat} (K : Type*) [Field K]
    [Fintype K] [DecidableEq K] [Algebra BinaryField K]
    [FiniteDimensional BinaryField K] [Finite K]
    (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K)
    (A : Finset (FieldTriple K)) (U : Submodule BinaryField (KTriple K))
    (b : (Fin 4 → FieldTriple K) → Basis (Fin s) BinaryField K) :
    (actualFiveGoodTapeSet K Q A U b).card =
      (goodFiveTupleSigma K A U b).card := by
  simp [actualFiveGoodTapeSet]

private theorem card_binaryVector_exact (n : Nat) :
    Fintype.card (BinaryVector n) = 2 ^ n := by
  have hdim : Module.finrank (ZMod 2) (BinaryVector n) = n := by
    rw [Module.finrank_eq_card_basis (Pi.basisFun (ZMod 2) (Fin n))]
    simp
  rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := BinaryVector n), hdim]
  norm_num

/-- The five-word fair-bit source has exactly `2^(13*s)` equally likely
tapes, matching the semantic tuple space through the explicit equivalence. -/
theorem card_fiveWordTape (s : Nat) :
    Fintype.card (FiveWordTape s) = 2 ^ (13 * s) := by
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    card_binaryVector_exact, card_binaryVector_exact]
  rw [← pow_mul]
  rw [← pow_add]
  congr 1
  ring

end

end CorruptedFieldRecovery
