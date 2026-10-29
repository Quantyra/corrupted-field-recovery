import CorruptedFieldRecovery.BinaryTensor
import CorruptedFieldRecovery.Defect

/-! Finite coefficient checking for a serialized compatible-plus-supported
representation.  This module proves the checker-to-semantics implication.  It
does not prove that a supplied compatible tensor is a trace-determinant tensor;
that is a separate field/coordinate validation obligation.
-/

namespace CorruptedFieldRecovery

/-- Semantic payload for the two summands of a compatible representation.
`compatible` is the candidate field-compatible tensor.  `residual` is an
alternating tensor on the certificate's support coordinates, pulled back by
the listed support map. -/
structure RepresentationPayload (n R : ℕ) where
  supportDim : ℕ
  supportDim_le : supportDim ≤ R
  compatible : BinaryTensor n
  compatible_alternating : IsAlternating compatible
  supportMap : BinaryVector n →ₗ[ZMod 2] BinaryVector supportDim
  supportMap_surjective : Function.Surjective supportMap
  residual : BinaryTensor supportDim
  residual_alternating : IsAlternating residual

/-- The tensor represented by a payload. -/
def RepresentationPayload.tensor {n R : ℕ} (cert : RepresentationPayload n R) :
    BinaryTensor n := cert.compatible + pullback cert.residual cert.supportMap

theorem RepresentationPayload.tensor_alternating {n R : ℕ}
    (cert : RepresentationPayload n R) : IsAlternating cert.tensor := by
  constructor
  · intro x y
    change cert.compatible x x y + cert.residual (cert.supportMap x)
      (cert.supportMap x) (cert.supportMap y) = 0
    rw [cert.compatible_alternating.1, cert.residual_alternating.1]
    exact zero_add 0
  constructor
  · intro x y
    change cert.compatible x y x + cert.residual (cert.supportMap x)
      (cert.supportMap y) (cert.supportMap x) = 0
    rw [cert.compatible_alternating.2.1, cert.residual_alternating.2.1]
    exact zero_add 0
  · intro x y
    change cert.compatible x y y + cert.residual (cert.supportMap x)
      (cert.supportMap y) (cert.supportMap y) = 0
    rw [cert.compatible_alternating.2.2, cert.residual_alternating.2.2]
    exact zero_add 0

/-- The finite Boolean checker compares every strictly increasing basis triple.
The quantifiers range over `Fin n`, so this is a finite computation. -/
noncomputable def increasingCoefficientCheck {n R : ℕ}
    (input : BinaryTensor n) (cert : RepresentationPayload n R) : Bool := by
  classical
  exact decide (∀ i j k : Fin n, i < j → j < k →
    coefficient input i j k = coefficient cert.tensor i j k)

/-- Acceptance of all increasing coefficients implies exact equality on every
triple of physical vectors.  This is unconditional in `R` and makes no
uniqueness or planted-witness claim. -/
theorem accepted_certificate_sound {n R : ℕ} (input : BinaryTensor n)
    (input_alternating : IsAlternating input)
    (cert : RepresentationPayload n R)
    (accepted : increasingCoefficientCheck input cert = true) :
    ∀ x y z, input x y z = cert.tensor x y z := by
  have hcoeff : ∀ i j k : Fin n, i < j → j < k →
      coefficient input i j k = coefficient cert.tensor i j k := by
    classical
    exact of_decide_eq_true accepted
  have h := binaryTensor_ext_of_increasing_coefficients input_alternating
    cert.tensor_alternating hcoeff
  intro x y z
  exact congrArg (fun t : BinaryTensor n => t x y z) h

end CorruptedFieldRecovery
