import CorruptedFieldRecovery.S010ObservedCleanTensor
import CorruptedFieldRecovery.S010ModeImageAlignedHiddenBalance
import Mathlib.Tactic

namespace CorruptedFieldRecovery

noncomputable section

/-- Coordinate casts along a free equality `p = 2`. -/
private def inputToBinaryCast {p n : Nat} (hp : p = 2)
    (x : Fin n → ZMod p) : BinaryVector n :=
  Equiv.cast (congrArg (fun q => Fin n → ZMod q) hp) x

private def binaryToInputCast {p n : Nat} (hp : p = 2)
    (x : BinaryVector n) : Fin n → ZMod p :=
  Equiv.cast (congrArg (fun q => Fin n → ZMod q) hp.symm) x

private theorem inputCast_binaryCast_cancel {p n : Nat} (hp : p = 2)
    (x : BinaryVector n) : inputToBinaryCast hp (binaryToInputCast hp x) = x := by
  cases hp
  rfl

/-- Transport a physical binary-linear endomorphism to the manuscript's input
space over `ZMod p`, using the derived `p = 2` coordinate equivalence. -/
private def physicalEndomorphismToInput
    {p n : Nat} (hp : p = 2)
    (T : Module.End (ZMod 2) (BinaryVector n)) :
    Module.End (ZMod p) (Fin n → ZMod p) where
  toFun x := binaryToInputCast hp (T (inputToBinaryCast hp x))
  map_add' := by
    intro x y
    cases hp
    simp [inputToBinaryCast, binaryToInputCast, map_add]
  map_smul' := by
    intro a x
    cases hp
    simp [inputToBinaryCast, binaryToInputCast, map_smul]

private theorem physicalEndomorphismToInput_apply
    {p n : Nat} (hp : p = 2)
    (T : Module.End (ZMod 2) (BinaryVector n)) (x : Fin n → ZMod p) :
    physicalEndomorphismToInput hp T x =
      binaryToInputCast hp (T (inputToBinaryCast hp x)) := rfl

/-- Pointwise, the Q-derived input equivalence sends a transported physical
endomorphism to Q applied to the original physical endomorphism. This derives
the scalar-ring and input-map correspondence from `ringChar K = 2`. -/
theorem modeImage_inputEquiv_from_Q_transport_endomorphism
    {K : Type*} [Field K] [CharP K 2]
    [Algebra BinaryField K] [Algebra (ZMod (ringChar K)) K]
    {s : Nat} (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K)
    (T : Module.End (ZMod 2) (BinaryVector (3 * s)))
    (x : BinaryInput K (3 * s)) :
    modeImage_inputEquiv_from_Q Q (physicalEndomorphismToInput
      (ringChar.eq K 2) T x) =
      Q (T (modeImage_inputVectorToBinary (K := K) x)) := by
  have hcancel (y : BinaryVector (3 * s)) :
      modeImage_inputVectorToBinary (K := K)
        (binaryToInputCast (ringChar.eq K 2) y) = y := by
    change inputToBinaryCast (ringChar.eq K 2)
      (binaryToInputCast (ringChar.eq K 2) y) = y
    exact inputCast_binaryCast_cancel (ringChar.eq K 2) y
  have hcast (y : BinaryInput K (3 * s)) :
      Equiv.cast (congrArg (fun p => Fin (3 * s) → ZMod p) (ringChar.eq K 2)) y =
        modeImage_inputVectorToBinary (K := K) y := rfl
  rw [modeImage_inputEquiv_from_Q_apply]
  rw [physicalEndomorphismToInput_apply, hcast]
  have hcoord : modeImage_inputVectorToBinary (K := K)
        (binaryToInputCast (ringChar.eq K 2)
          (T (inputToBinaryCast (ringChar.eq K 2) x))) =
      T (modeImage_inputVectorToBinary (K := K) x) := by
    rw [hcancel]
    exact congrArg T rfl
  rw [hcoord]

/-- On vectors in `Q` coordinates, the clean physical tensor is precisely the
trace-determinant contraction used by the hidden sampled-basis equations. -/
theorem qTraceDeterminantTensor_apply
    {K : Type*} [Field K] [Finite K] [Algebra BinaryField K]
    {n : Nat} (Q : BinaryVector n ≃ₗ[BinaryField] FieldTriple K) (c : K)
    (x y z : BinaryVector n) :
    qTraceDeterminantTensor Q c x y z =
      Algebra.trace BinaryField K (c * fieldDet3 (Q x) (Q y) (Q z)) := rfl

end

end CorruptedFieldRecovery
