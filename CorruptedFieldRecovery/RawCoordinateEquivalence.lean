import CorruptedFieldRecovery.RawFieldQuotient
import CorruptedFieldRecovery.BinaryTensor

/-! Finite array checker for a square binary coordinate transform and a
serialized two-sided inverse. -/

namespace CorruptedFieldRecovery

abbrev RawCoordinateMatrix := Array (ZMod 2)

def rawCoordinateMatrixOffset (n : Nat) (i j : Fin n) : Nat := i.val * n + j.val

def rawCoordinateUnitVector {n : Nat} (i : Fin n) : BinaryVector n :=
  fun j => if j = i then 1 else 0

/-- Interpret a row-major binary matrix as a linear map on `Fin n` vectors. -/
def rawCoordinateMatrixMap {n : Nat} (matrix : RawCoordinateMatrix) :
    BinaryVector n →ₗ[ZMod 2] BinaryVector n where
  toFun x i := ∑ j : Fin n, matrix[rawCoordinateMatrixOffset n i j]! * x j
  map_add' x y := by
    ext i
    simp [Finset.sum_add_distrib, mul_add]
  map_smul' c x := by
    ext i
    simp [Finset.mul_sum, mul_assoc, mul_comm]

/-- The checker validates both finite matrix products on the standard basis.
Together with the two dense-size checks, this is the actual serialized
invertibility gate. -/
def rawCoordinateMatrixCheck {n : Nat}
    (forward inverse : RawCoordinateMatrix) : Bool :=
  decide (forward.size = n * n) &&
    decide (inverse.size = n * n) &&
    decide (∀ i : Fin n,
      rawCoordinateMatrixMap inverse
        (rawCoordinateMatrixMap forward (rawCoordinateUnitVector i)) =
        rawCoordinateUnitVector i) &&
    decide (∀ i : Fin n,
      rawCoordinateMatrixMap forward
        (rawCoordinateMatrixMap inverse (rawCoordinateUnitVector i)) =
        rawCoordinateUnitVector i)

theorem accepted_rawCoordinateMatrixCheck_compositions {n : Nat}
    (forward inverse : RawCoordinateMatrix)
    (hcheck : rawCoordinateMatrixCheck (n := n) forward inverse = true) :
    (rawCoordinateMatrixMap (n := n) inverse).comp (rawCoordinateMatrixMap (n := n) forward) =
        LinearMap.id ∧
      (rawCoordinateMatrixMap (n := n) forward).comp (rawCoordinateMatrixMap (n := n) inverse) =
        LinearMap.id := by
  classical
  simp only [rawCoordinateMatrixCheck, Bool.and_eq_true] at hcheck
  have hleft : ∀ i : Fin n,
      rawCoordinateMatrixMap (n := n) inverse
        (rawCoordinateMatrixMap (n := n) forward (rawCoordinateUnitVector i)) =
        rawCoordinateUnitVector i := of_decide_eq_true hcheck.1.2
  have hright : ∀ i : Fin n,
      rawCoordinateMatrixMap (n := n) forward
        (rawCoordinateMatrixMap (n := n) inverse (rawCoordinateUnitVector i)) =
        rawCoordinateUnitVector i := of_decide_eq_true hcheck.2
  constructor
  · apply (Pi.basisFun (ZMod 2) (Fin n)).ext
    intro i
    have hunit : (Pi.basisFun (ZMod 2) (Fin n)) i = rawCoordinateUnitVector i := by
      ext j
      simp [rawCoordinateUnitVector, Pi.single_apply]
    simpa [LinearMap.comp_apply, hunit] using hleft i
  · apply (Pi.basisFun (ZMod 2) (Fin n)).ext
    intro i
    have hunit : (Pi.basisFun (ZMod 2) (Fin n)) i = rawCoordinateUnitVector i := by
      ext j
      simp [rawCoordinateUnitVector, Pi.single_apply]
    simpa [LinearMap.comp_apply, hunit] using hright i

noncomputable def accepted_rawCoordinateMatrixEquiv {n : Nat}
    (forward inverse : RawCoordinateMatrix)
    (hcheck : rawCoordinateMatrixCheck (n := n) forward inverse = true) :
    BinaryVector n ≃ₗ[ZMod 2] BinaryVector n :=
  LinearEquiv.ofBijective (rawCoordinateMatrixMap (n := n) forward) (by
    have hcomp := accepted_rawCoordinateMatrixCheck_compositions forward inverse hcheck
    refine ⟨?_, ?_⟩
    · intro x y hxy
      have hleft := congrArg (rawCoordinateMatrixMap (n := n) inverse) hxy
      have hx := congrArg (fun f : BinaryVector n →ₗ[ZMod 2] BinaryVector n => f x) hcomp.1
      have hy := congrArg (fun f : BinaryVector n →ₗ[ZMod 2] BinaryVector n => f y) hcomp.1
      calc
        x = rawCoordinateMatrixMap (n := n) inverse
          (rawCoordinateMatrixMap (n := n) forward x) := by
          simpa [LinearMap.comp_apply] using hx.symm
        _ = rawCoordinateMatrixMap (n := n) inverse
            (rawCoordinateMatrixMap (n := n) forward y) := hleft
        _ = y := by simpa [LinearMap.comp_apply] using hy
    · intro y
      refine ⟨rawCoordinateMatrixMap (n := n) inverse y, ?_⟩
      have hright := congrArg
        (fun f : BinaryVector n →ₗ[ZMod 2] BinaryVector n => f y) hcomp.2
      simpa [LinearMap.comp_apply] using hright)

end CorruptedFieldRecovery
