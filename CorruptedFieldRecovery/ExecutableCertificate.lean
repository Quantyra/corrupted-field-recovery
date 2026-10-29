import CorruptedFieldRecovery.DenseInput
import CorruptedFieldRecovery.CertificateSoundness

/-! An array-backed coefficient gate for a serialized compatible-plus-residual
candidate. The operational checker reads only the finite arrays; the semantic
tensor and bridge fields in the input structures state the separate proof
obligations from serialized finite arithmetic to tensor semantics. -/

namespace CorruptedFieldRecovery

/-- The dense ordered coefficient table, stored in row-major order. -/
abbrev CoefficientArray := Array (ZMod 2)

/-- Row-major position of an ordered coefficient triple. -/
def coefficientOffset (n : Nat) (i j k : Fin n) : Nat :=
  (i.val * n + j.val) * n + k.val

/-- A serialized representation: arrays for the candidate compatible tensor
and residual tensor, and a computed array for their coefficientwise sum.
All three arrays are ordinary finite arrays, not semantic functions. -/
structure ExecutableCertificate (n R : Nat) where
  supportDim : Nat
  supportDim_le : supportDim ≤ R
  compatibleCoefficients : CoefficientArray
  residualCoefficients : CoefficientArray
  representedCoefficients : CoefficientArray
  arrays_agree : representedCoefficients =
    compatibleCoefficients.mapIdx (fun i x => x + residualCoefficients[i]!)
  compatibleTensor : BinaryTensor n
  compatibleTensor_alternating : IsAlternating compatibleTensor
  residualTensor : BinaryTensor n
  residualTensor_alternating : IsAlternating residualTensor
  representedTensor : BinaryTensor n
  representedTensor_eq : representedTensor = compatibleTensor + residualTensor
  represented_bridge : ∀ i j k : Fin n,
    coefficient representedTensor i j k =
      representedCoefficients[coefficientOffset n i j k]!

/-- The input is supplied as an actual dense ordered coefficient array. -/
structure ExecutableInput (n : Nat) where
  coefficients : CoefficientArray
  tensor : BinaryTensor n
  tensor_alternating : IsAlternating tensor
  tensor_bridge : ∀ i j k : Fin n,
    coefficient tensor i j k = coefficients[coefficientOffset n i j k]!

/-- Executable finite-array comparison. `Array ==` traverses the actual
serialized arrays and returns false when their lengths or entries differ. -/
def executableCoefficientCheck {n R : Nat}
    (input : ExecutableInput n) (cert : ExecutableCertificate n R) : Bool :=
  decide (input.coefficients.size = n * n * n) &&
    decide (cert.compatibleCoefficients.size = n * n * n) &&
    decide (cert.residualCoefficients.size = n * n * n) &&
    decide (cert.representedCoefficients.size = n * n * n) &&
    (input.coefficients == cert.representedCoefficients)

/-- Acceptance implies equality of every ordered coefficient. -/
theorem accepted_executable_coefficients {n R : Nat}
    (input : ExecutableInput n) (cert : ExecutableCertificate n R)
    (accepted : executableCoefficientCheck input cert = true) :
    ∀ i j k : Fin n,
      coefficient input.tensor i j k = coefficient cert.representedTensor i j k := by
  intro i j k
  simp only [executableCoefficientCheck, Bool.and_eq_true] at accepted
  have hEq : (input.coefficients == cert.representedCoefficients) = true :=
    accepted.2
  have harr : input.coefficients = cert.representedCoefficients :=
    eq_of_beq hEq
  rw [input.tensor_bridge, cert.represented_bridge]
  have hget := congrArg (fun a : CoefficientArray => a[coefficientOffset n i j k]!) harr
  exact hget

/-- Actual-array checker soundness on all vectors.  The candidate semantics
must already bridge the finite compatible and residual arrays; establishing
that bridge (including field, coordinate, nonzero and support validation) is
separate from this coefficient gate. -/
theorem accepted_executable_certificate_sound {n R : Nat}
    (input : ExecutableInput n) (cert : ExecutableCertificate n R)
    (accepted : executableCoefficientCheck input cert = true) :
    ∀ x y z, input.tensor x y z = cert.representedTensor x y z := by
  have hcoeff := accepted_executable_coefficients input cert accepted
  have h := binaryTensor_ext_of_coefficients hcoeff
  intro x y z
  exact congrArg (fun t : BinaryTensor n => t x y z) h

end CorruptedFieldRecovery
