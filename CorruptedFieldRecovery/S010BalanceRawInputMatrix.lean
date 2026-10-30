import CorruptedFieldRecovery.S010BalanceComputableMatrix
import CorruptedFieldRecovery.RawCertificate
import Mathlib.Tactic

namespace CorruptedFieldRecovery

/-- The computable constraint matrix built directly from the manuscript's raw
alternating coefficient array. `decodeRawArray` is the same finite minor-sum
decoder used by the executable certificate path. -/
def actualBalanceRawInputCoefficientMatrix {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s) :
    Matrix (ActualBalanceBasisRow s) (Fin (3 * s) × Fin (3 * s)) (ZMod 2) :=
  actualBalanceComputableCoefficientMatrix (decodeRawArray (n := 3 * s) raw) tape

/-- The serialized row at a specified row-list position is the array of
coefficients at the declared column-list order. -/
theorem actualBalanceSerializedCoefficientMatrix_row_spec {s : Nat}
    (A : BinaryTensor (3 * s)) (tape : FiveWordTape s)
    (ri ci : Nat) (row : ActualBalanceBasisRow s)
    (col : Fin (3 * s) × Fin (3 * s))
    (hr : (actualBalanceRowList s)[ri]? = some row)
    (hc : (actualBalanceColumnList s)[ci]? = some col) :
    ((actualBalanceSerializedCoefficientMatrix A tape)[ri]?.bind
      fun r => r[ci]?) =
        some (actualBalanceComputableCoefficientMatrix A tape row col) := by
  simp [actualBalanceSerializedCoefficientMatrix, hr, hc]

/-- The serializer's outer size is exactly the declared row enumeration size. -/
theorem actualBalanceSerializedCoefficientMatrix_outer_size {s : Nat}
    (A : BinaryTensor (3 * s)) (tape : FiveWordTape s) :
    (actualBalanceSerializedCoefficientMatrix A tape).size =
      (actualBalanceRowList s).length :=
  actualBalanceSerializedCoefficientMatrix_size A tape

/-- Build a finite Boolean checker for the balance equations on a raw input
array. The dense length condition is checked before tensor decoding is used. -/
def actualBalanceRawInputConstraintCheck {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s)
    (T : Module.End (ZMod 2) (BinaryVector (3 * s))) : Bool :=
  decide (raw.size = (3 * s) * (3 * s) * (3 * s)) &&
    actualBalanceBasisMatrixCheck (decodeRawArray (n := 3 * s) raw) tape T

theorem actualBalanceRawInputConstraintCheck_iff {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s)
    (T : Module.End (ZMod 2) (BinaryVector (3 * s))) :
    actualBalanceRawInputConstraintCheck raw tape T = true ↔
      raw.size = (3 * s) * (3 * s) * (3 * s) ∧
        actualFourBilinearBalanced (decodeRawArray (n := 3 * s) raw) tape T := by
  simp [actualBalanceRawInputConstraintCheck, actualBalanceBasisMatrixCheck_iff]
  intro _
  constructor
  · intro hzero
    exact (actualBalanceBasisMatrix_ker_iff
      (decodeRawArray (n := 3 * s) raw) tape T).1
      (LinearMap.mem_ker.mpr hzero)
  · intro hbal
    exact LinearMap.mem_ker.mp
      ((actualBalanceBasisMatrix_ker_iff
        (decodeRawArray (n := 3 * s) raw) tape T).2 hbal)

/-- The raw-input matrix has the same executable coefficient-cell meaning as
the tensor-built matrix, now with its source array made explicit. -/
theorem actualBalanceRawInputMatrix_eq_decoded {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s) :
    actualBalanceRawInputCoefficientMatrix raw tape =
      actualBalanceComputableCoefficientMatrix (decodeRawArray (n := 3 * s) raw) tape := rfl

end CorruptedFieldRecovery