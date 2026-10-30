import CorruptedFieldRecovery.BinaryFieldTransport
import CorruptedFieldRecovery.ProperSubfieldCounts
import CorruptedFieldRecovery.BinaryTensor
import Mathlib.Tactic

namespace CorruptedFieldRecovery

noncomputable section

/-- A Q-coordinate map yields a linear equivalence from the physical binary
input to the field triple once a free-index equality p = 2 is supplied. The
argument keeps the change of coefficient ring explicit and aligns the two
algebra structures only by the uniqueness of ZMod-algebra structures. -/
private def binaryInputEquiv_of_index_eq_two
    {p : Nat} (K : Type*) [Field K]
    [Algebra (ZMod p) K] [Algebra BinaryField K]
    {n : Nat} (hp : p = 2)
    (Q : BinaryVector n ≃ₗ[BinaryField] FieldTriple K) :
    (Fin n → ZMod p) ≃ₗ[ZMod p] FieldTriple K := by
  subst p
  refine
    { toEquiv := Q.toEquiv
      map_add' := ?_
      map_smul' := ?_ }
  · intro x y
    exact Q.map_add x y
  · intro a x
    fin_cases a
    · calc
        Q (0 • x) = Q 0 := congrArg Q (zero_smul (ZMod 2) x)
        _ = 0 := map_zero Q
        _ = 0 • Q x := (zero_smul (ZMod 2) (Q x)).symm
    · calc
        Q (1 • x) = Q x := congrArg Q (one_smul (ZMod 2) x)
        _ = 1 • Q x := (one_smul (ZMod 2) (Q x)).symm

private theorem binaryInputEquiv_of_index_eq_two_apply
    {p : Nat} (K : Type*) [Field K]
    [Algebra (ZMod p) K] [Algebra BinaryField K]
    {n : Nat} (hp : p = 2)
    (Q : BinaryVector n ≃ₗ[BinaryField] FieldTriple K)
    (x : Fin n → ZMod p) :
    binaryInputEquiv_of_index_eq_two K hp Q x =
      Q (Equiv.cast (congrArg (fun q => Fin n → ZMod q) hp) x) := by
  subst p
  rfl

/-- The manuscript's field-coordinate isomorphism on `BinaryVector (3*s)`
also supplies the physical `BinaryInput` isomorphism required by the hidden
contraction theorem. This derivation uses `ringChar K = 2`; it does not assume
an unrelated input equivalence. -/
def modeImage_inputEquiv_from_Q
    {K : Type*} [Field K] [CharP K 2]
    [Algebra BinaryField K] [Algebra (ZMod (ringChar K)) K]
    {s : Nat}
    (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K) :
    BinaryInput K (3 * s) ≃ₗ[ZMod (ringChar K)] FieldTriple K := by
  exact binaryInputEquiv_of_index_eq_two (K := K) (p := ringChar K)
    (n := 3 * s) (ringChar.eq K 2) Q

/-- Pointwise, the Q-derived physical input equivalence is exactly Q after
casting each coordinate along the proved `ringChar K = 2` equality. -/
theorem modeImage_inputEquiv_from_Q_apply
    {K : Type*} [Field K] [CharP K 2]
    [Algebra BinaryField K] [Algebra (ZMod (ringChar K)) K]
    {s : Nat}
    (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K)
    (x : BinaryInput K (3 * s)) :
    modeImage_inputEquiv_from_Q Q x =
      Q (Equiv.cast
        (congrArg (fun p => Fin (3 * s) → ZMod p) (ringChar.eq K 2)) x) := by
  exact binaryInputEquiv_of_index_eq_two_apply K (ringChar.eq K 2) Q x

end

end CorruptedFieldRecovery
