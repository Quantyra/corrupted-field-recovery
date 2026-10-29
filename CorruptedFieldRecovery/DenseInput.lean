import CorruptedFieldRecovery.BinaryTensor
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic.Ring

/-! Computable dense-input codec indexed by increasing coordinate triples. -/

namespace CorruptedFieldRecovery

abbrev IncreasingTriple (n : ℕ) :=
  {t : ((Fin n × Fin n) × Fin n) // t.1.1 < t.1.2 ∧ t.1.2 < t.2}

abbrev DenseInputPayload (n : ℕ) := IncreasingTriple n → ZMod 2

def increasingTripleI {n : ℕ} (t : IncreasingTriple n) : Fin n := t.val.1.1

def increasingTripleJ {n : ℕ} (t : IncreasingTriple n) : Fin n := t.val.1.2

def increasingTripleK {n : ℕ} (t : IncreasingTriple n) : Fin n := t.val.2

/-- The computable coordinate unit vector used by the input encoder. -/
def coordinateVectorCode {n : ℕ} (i : Fin n) : BinaryVector n :=
  Pi.single i (1 : ZMod 2)

theorem coordinateVectorCode_eq_coordinateVector {n : ℕ} (i : Fin n) :
    coordinateVectorCode i = coordinateVector i := by
  simp [coordinateVectorCode, coordinateVector]

/-- A trilinear coordinate monomial `x_i y_j z_k`. -/
def coordinateMonomial {n : ℕ} (i j k : Fin n) : BinaryTensor n :=
  LinearMap.mk₂ (ZMod 2)
    (fun x y => (x i * y j) • (Pi.proj k : BinaryVector n →ₗ[ZMod 2] ZMod 2))
    (by
      intro x₁ x₂ y
      ext z
      simp [Pi.add_apply, add_mul, add_smul, mul_assoc]
      ring)
    (by
      intro c x y
      ext z
      simp [Pi.smul_apply, mul_assoc, smul_smul]
      ring)
    (by
      intro x y₁ y₂
      ext z
      simp [Pi.add_apply, mul_add, add_smul, mul_assoc]
      ring)
    (by
      intro c x y
      ext z
      simp [Pi.smul_apply, mul_assoc, smul_smul]
      ring)

@[simp]
theorem coordinateMonomial_apply {n : ℕ} (i j k : Fin n)
    (x y z : BinaryVector n) :
    coordinateMonomial i j k x y z = x i * y j * z k := by
  simp [coordinateMonomial, mul_assoc]

/-- The six-term determinant of the selected coordinate rows. In `F₂`, the
three negative Leibniz terms agree with addition. -/
def minorTensor {n : ℕ} (i j k : Fin n) : BinaryTensor n :=
  coordinateMonomial i j k + coordinateMonomial i k j +
  coordinateMonomial j i k + coordinateMonomial j k i +
  coordinateMonomial k i j + coordinateMonomial k j i

theorem minorTensor_apply {n : ℕ} (i j k : Fin n)
    (x y z : BinaryVector n) :
    minorTensor i j k x y z =
      x i * y j * z k + x i * y k * z j +
      x j * y i * z k + x j * y k * z i +
      x k * y i * z j + x k * y j * z i := by
  simp [minorTensor, add_assoc]

/-- Each coordinate minor is alternating in all three arguments. -/
theorem minorTensor_isAlternating {n : ℕ} (i j k : Fin n) :
    IsAlternating (minorTensor i j k) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x z
    rw [minorTensor_apply]
    ring_nf <;> norm_num
  · intro x y
    rw [minorTensor_apply]
    ring_nf <;> norm_num
  · intro x y
    rw [minorTensor_apply]
    ring_nf <;> norm_num

/-- Encode an alternating dense tensor by its strictly increasing coefficients. -/
def encodeDenseInput {n : ℕ} (C : BinaryTensor n) : DenseInputPayload n :=
  fun t => C (coordinateVectorCode (increasingTripleI t))
    (coordinateVectorCode (increasingTripleJ t)) (coordinateVectorCode (increasingTripleK t))

theorem encodeDenseInput_eq_semanticCoefficient {n : ℕ} (C : BinaryTensor n)
    (t : IncreasingTriple n) :
    encodeDenseInput C t =
      coefficient C (increasingTripleI t) (increasingTripleJ t) (increasingTripleK t) := by
  simp [encodeDenseInput, coefficient, coordinateVectorCode_eq_coordinateVector]

/-- Decode payload bits by summing their six-term determinant minors. -/
def decodeDenseInput {n : ℕ} (payload : DenseInputPayload n) : BinaryTensor n :=
  ∑ t : IncreasingTriple n,
    payload t • minorTensor (increasingTripleI t) (increasingTripleJ t) (increasingTripleK t)

end CorruptedFieldRecovery
