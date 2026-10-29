import CorruptedFieldRecovery.ProperSubfieldCounts
import CorruptedFieldRecovery.FourContractions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace CorruptedFieldRecovery

noncomputable section

/-- Semantic clean vectors annihilate a binary covector support subspace. -/
def cleanSupportSet {K : Type*} [Field K]
    [Algebra BinaryField K] [FiniteDimensional BinaryField K]
    [Fintype (FieldTriple K)] [DecidableEq (FieldTriple K)]
    (W : Submodule BinaryField (Module.Dual BinaryField (FieldTriple K))) :
    Finset (FieldTriple K) := by
  classical
  exact Finset.univ.filter fun x => x ∈ W.dualCoannihilator

/-- The clean-set cardinality follows from the dual-coannihilator dimension
formula. The trace pairing and its transport determine W in an application;
this count uses only its actual binary support rank. -/
theorem cleanSupportSet_card
    (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    [Algebra BinaryField K] [FiniteDimensional BinaryField K]
    (s r : Nat) (hs : Module.finrank BinaryField K = s)
    (W : Submodule BinaryField (Module.Dual BinaryField (FieldTriple K)))
    (hW : Module.finrank BinaryField W = r) :
    (cleanSupportSet (K := K) W).card = 2 ^ (3 * s - r) := by
  classical
  have hV : Module.finrank BinaryField (FieldTriple K) = 3 * s := by
    change Module.finrank BinaryField (K × (K × K)) = 3 * s
    rw [Module.finrank_prod, Module.finrank_prod, hs]
    omega
  have hcoann : Module.finrank BinaryField W.dualCoannihilator = 3 * s - r := by
    have hsum := Subspace.finrank_add_finrank_dualCoannihilator_eq W
    rw [hW, hV] at hsum
    omega
  have hcardV : Fintype.card W.dualCoannihilator = 2 ^ (3 * s - r) := by
    rw [Module.card_eq_pow_finrank (K := BinaryField)
      (V := W.dualCoannihilator), hcoann]
    simp [BinaryField]
  have hcardA : (cleanSupportSet (K := K) W).card =
      Fintype.card W.dualCoannihilator := by
    simp [cleanSupportSet, Fintype.card_subtype]
  rw [hcardA, hcardV]

end

end CorruptedFieldRecovery
