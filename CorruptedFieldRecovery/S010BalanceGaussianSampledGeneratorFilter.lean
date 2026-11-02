import CorruptedFieldRecovery.S010BalanceGaussianOrderedSeedIndex
import CorruptedFieldRecovery.RawRabinCandidateCorrectness
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.PrimitiveElement

/-! Bridge the actual coefficient-combination sampler to the generator test.

The result is deliberately conditional on the checks performed by the
manuscript algorithm.  The good-event hypotheses put the sampled endomorphism
in the Q-conjugated scalar space; the recurrence and serialized-modulus
equality connect the computed powers to the raw Rabin gate.  Passing that gate
then proves that the sampled scalar generates K.  Nothing here says every
seed passes: in particular, the seed for scalar one is present and is not a
generator when the extension degree exceeds one.
-/

namespace CorruptedFieldRecovery

open Polynomial

/-- Conjugation by Q preserves products as well as the linear structure.  This
is the algebra map needed to transport a recurrence for the sampled
endomorphism back to its sampled field scalar. -/
noncomputable def qScalarConjugateAlgHom
    {K : Type*} [Field K] [Algebra BinaryField K] {n : Nat}
    (Q : BinaryVector n ≃ₗ[BinaryField] FieldTriple K) :
    K →ₐ[BinaryField] Module.End BinaryField (BinaryVector n) where
  toFun := qScalarConjugateLinearMap Q
  map_zero' := map_zero (qScalarConjugateLinearMap Q)
  map_add' := map_add (qScalarConjugateLinearMap Q)
  map_one' := by
    apply LinearMap.ext
    intro x
    simp [qScalarConjugateLinearMap]
  map_mul' := by
    intro a b
    apply LinearMap.ext
    intro x
    simp [qScalarConjugateLinearMap, smul_smul]
  commutes' := by
    intro a
    apply LinearMap.ext
    intro x
    simp only [qScalarConjugateLinearMap]
    rw [map_smul, LinearEquiv.symm_apply_apply]
    simp [Algebra.smul_def]

/-- The polynomial made from the recurrence coefficients computed by the
manuscript's power-relation solve.  The minus sign is the conventional
characteristic-polynomial convention; over BinaryField it agrees with plus. -/
noncomputable def actualBalanceGaussianRecurrencePolynomial {s : Nat}
    (coefficients : Fin s → BinaryField) : Polynomial BinaryField :=
  X ^ s - ∑ j : Fin s, C (coefficients j) * X ^ j.val

/-- Evaluating the recurrence polynomial at an endomorphism is exactly the
left side minus the solved linear combination of the first s powers. -/
theorem actualBalanceGaussianRecurrencePolynomial_aeval
    {s : Nat} (coefficients : Fin s → BinaryField)
    (T : Module.End BinaryField (BinaryVector (3 * s))) :
    Polynomial.aeval T (actualBalanceGaussianRecurrencePolynomial coefficients) =
      T ^ s - ∑ j : Fin s, coefficients j • T ^ j.val := by
  simp [actualBalanceGaussianRecurrencePolynomial, Algebra.smul_def]

/-- Exact evidence produced by the manuscript's sampled-generator gate.

`powersIndependent` records its separate first-s-powers rank test.
`recurrence` records the solved T^s relation, while `encodedModulus` is the
required connection from that relation to the bits submitted to Rabin.
`shapeAccepted` and `rabinAccepted` are the actual finite checks.  The scalar
field in `candidate.scalar` is the later representation coefficient; it is
not the sampled generator parameter. -/
structure ActualBalanceGaussianGeneratorFilterPass
    {K : Type*} [Field K] [Algebra BinaryField K]
    {s : Nat}
    (candidate : RawFieldCandidate s)
    (coefficients : Fin s → BinaryField)
    (T : Module.End BinaryField (BinaryVector (3 * s))) : Prop where
  powersIndependent :
    LinearIndependent BinaryField (fun i : Fin s => T ^ i.val)
  recurrence :
    T ^ s = ∑ j : Fin s, coefficients j • T ^ j.val
  encodedModulus :
    rawMaskPolynomial (rawFieldBitsToNat candidate.modulus) =
      actualBalanceGaussianRecurrencePolynomial coefficients
  shapeAccepted : rawFieldCandidateShapeCheck candidate = true
  rabinAccepted : rawCandidateRabinCheck candidate = true

/-- Build the explicit filter evidence from the executable fast-check result
and the separate power-independence test.  The recurrence and bit-to-
polynomial equality still have to be supplied by the matrix solver/serializer
refinement. -/
theorem actualBalanceGaussianGeneratorFilterPass_of_fastCheck
    {K : Type*} [Field K] [Algebra BinaryField K]
    {s : Nat} (candidate : RawFieldCandidate s)
    (coefficients : Fin s → BinaryField)
    (T : Module.End BinaryField (BinaryVector (3 * s)))
    (hpowers : LinearIndependent BinaryField (fun i : Fin s => T ^ i.val))
    (hrecurrence :
      T ^ s = ∑ j : Fin s, coefficients j • T ^ j.val)
    (hencoded :
      rawMaskPolynomial (rawFieldBitsToNat candidate.modulus) =
        actualBalanceGaussianRecurrencePolynomial coefficients)
    (hfast : rawFieldCandidateFastCheck candidate = true) :
    ActualBalanceGaussianGeneratorFilterPass candidate coefficients T := by
  simp only [rawFieldCandidateFastCheck, Bool.and_eq_true] at hfast
  exact ⟨hpowers, hrecurrence, hencoded, hfast.1, hfast.2⟩

/-- A polynomial root transported across the Q-conjugation algebra map. -/
theorem aeval_qScalarConjugate_eq_zero_iff
    {K : Type*} [Field K] [Algebra BinaryField K] {n : Nat}
    (Q : BinaryVector n ≃ₗ[BinaryField] FieldTriple K)
    (k : K) (p : Polynomial BinaryField) :
    Polynomial.aeval (qScalarConjugateLinearMap Q k) p = 0 ↔
      Polynomial.aeval k p = 0 := by
  have heval :
      Polynomial.aeval (qScalarConjugateLinearMap Q k) p =
        qScalarConjugateLinearMap Q (Polynomial.aeval k p) := by
    rw [Polynomial.aeval_algHom (qScalarConjugateAlgHom Q) k]
    rfl
  constructor
  · intro h
    apply qScalarConjugateLinearMap_injective Q
    rw [map_zero]
    exact heval.symm.trans h.symm
  · intro h
    rw [heval, h, map_zero]

/-- If the actual raw Rabin gate accepts the encoded recurrence polynomial,
then the sampled scalar has that polynomial as its minimal polynomial and is a
primitive element of K.  The hypotheses state the pass conditions; this does
not assume or claim that a randomly selected seed passes them. -/
theorem actualBalanceGaussianSampledScalar_primitive_of_filterPass
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Finite K]
    [CharP K 2] [Algebra BinaryField K] [FiniteDimensional BinaryField K]
    {s : Nat}
    (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K)
    (candidate : RawFieldCandidate s)
    (coefficients : Fin s → BinaryField)
    (T : Module.End BinaryField (BinaryVector (3 * s)))
    (hT : T ∈ qScalarConjugateEndRange Q)
    (hpass : ActualBalanceGaussianGeneratorFilterPass candidate coefficients T)
    (hK : Module.finrank BinaryField K = s) :
    let k := actualBalanceGaussianQScalarParameter Q T
    actualBalanceGaussianRecurrencePolynomial coefficients = minpoly BinaryField k ∧
      Algebra.adjoin BinaryField ({k} : Set K) = ⊤ ∧
      LinearIndependent BinaryField (fun i : Fin s => T ^ i.val) := by
  let k := actualBalanceGaussianQScalarParameter Q T
  let p := actualBalanceGaussianRecurrencePolynomial coefficients
  have hconj : qScalarConjugateLinearMap Q k = T :=
    actualBalanceGaussianQScalarParameter_spec Q hT
  have hrootT : Polynomial.aeval T p = 0 := by
    rw [actualBalanceGaussianRecurrencePolynomial_aeval]
    rw [hpass.recurrence]
    simp
  have hrootK : Polynomial.aeval k p = 0 := by
    apply (aeval_qScalarConjugate_eq_zero_iff Q k p).mp
    simpa [hconj] using hrootT
  have hmod := rawFieldCandidateShapeCheck_modulus_polynomial
    candidate hpass.shapeAccepted
  have hpolyIrr :=
    (rawCandidateRabinCheck_eq_true_iff_irreducible candidate
      hpass.shapeAccepted).mp hpass.rabinAccepted
  have hmonic : p.Monic := by
    rw [← hpass.encodedModulus]
    exact hmod.1
  have hirr : Irreducible p := by
    rw [← hpass.encodedModulus]
    exact hpolyIrr
  have hminpoly : p = minpoly BinaryField k :=
    minpoly.eq_of_irreducible_of_monic hirr hrootK hmonic
  have hdegree : p.natDegree = s := by
    rw [← hpass.encodedModulus]
    exact hmod.2
  have hminDegree : (minpoly BinaryField k).natDegree =
      Module.finrank BinaryField K := by
    rw [← hminpoly]
    exact hdegree.trans hK.symm
  have hprimitive : Algebra.adjoin BinaryField ({k} : Set K) = ⊤ :=
    (Field.primitive_element_iff_minpoly_natDegree_eq
      (F := BinaryField) (E := K) k).2 hminDegree
  exact ⟨hminpoly, hprimitive, hpass.powersIndependent⟩

/-- The selector used by the raw array path really does produce an element of
the Q-scalar range on a good tape under the explicit model promise.  This is
the input bridge for the conditional generator-filter theorem above. -/
theorem actualBalanceGaussianArrayFlagSelectBySeed_mem_qScalarRange
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Finite K]
    [CharP K 2] [Algebra BinaryField K] [FiniteDimensional BinaryField K]
    [Algebra (ZMod (ringChar K)) K]
    {s : Nat}
    (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K)
    (E : BinaryTensor (3 * s))
    (U : Submodule BinaryField (KTriple K))
    (b : (Fin 4 → FieldTriple K) → Module.Basis (Fin s) BinaryField K)
    (raw : RawCoefficientArray) (tape : FiveWordTape s)
    (htape : tape ∈ actualFiveGoodTapeSet K Q
      (modeImageSemanticCleanFieldSet Q E) U b)
    (c : K) (hc : c ≠ 0)
    (hmodel : HasObservedTraceDeterminantDecomposition
      (decodeRawArray (n := 3 * s) raw) E LinearMap.id Q c)
    (hsize : raw.size = (3 * s) * (3 * s) * (3 * s))
    (hK : Module.finrank BinaryField K = s)
    (seed : Fin s → BinaryField) :
    actualBalanceGaussianArrayFlagSelectBySeed raw tape
      (actualBalanceGaussianRawFreeIndex_card_eq
          Q E U b raw tape htape c hc hmodel hsize hK) seed ∈ qScalarConjugateEndRange Q := by
  let hcard : Fintype.card (actualBalanceGaussianRawFreeIndex raw tape) = s :=
    actualBalanceGaussianRawFreeIndex_card_eq
      Q E U b raw tape htape c hc hmodel hsize hK
  unfold actualBalanceGaussianArrayFlagSelectBySeed
  exact actualBalanceGaussianRawWeightedCombination_mem_qScalarRange
    Q E U b raw tape htape c hc hmodel hsize
    (fun free => seed ((actualBalanceGaussianRawFreeIndexFinEquiv
      raw tape hcard).symm free))

/-- Full conditional theorem for the actual ordered-array sample.  A caller
must provide the genuine recurrence, independence check, and successful raw
shape/Rabin checks for this selected T; failure on some seeds remains
possible. -/
theorem actualBalanceGaussianArrayFlagSampledGenerator_of_filterPass
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Finite K]
    [CharP K 2] [Algebra BinaryField K] [FiniteDimensional BinaryField K]
    [Algebra (ZMod (ringChar K)) K]
    {s : Nat}
    (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K)
    (E : BinaryTensor (3 * s))
    (U : Submodule BinaryField (KTriple K))
    (b : (Fin 4 → FieldTriple K) → Module.Basis (Fin s) BinaryField K)
    (raw : RawCoefficientArray) (tape : FiveWordTape s)
    (htape : tape ∈ actualFiveGoodTapeSet K Q
      (modeImageSemanticCleanFieldSet Q E) U b)
    (c : K) (hc : c ≠ 0)
    (hmodel : HasObservedTraceDeterminantDecomposition
      (decodeRawArray (n := 3 * s) raw) E LinearMap.id Q c)
    (hsize : raw.size = (3 * s) * (3 * s) * (3 * s))
    (hK : Module.finrank BinaryField K = s)
    (seed : Fin s → BinaryField)
    (candidate : RawFieldCandidate s)
    (coefficients : Fin s → BinaryField)
    (hpass : ActualBalanceGaussianGeneratorFilterPass candidate coefficients
      (actualBalanceGaussianArrayFlagSelectBySeed raw tape
        (actualBalanceGaussianRawFreeIndex_card_eq
            Q E U b raw tape htape c hc hmodel hsize hK) seed)) :
    let k := actualBalanceGaussianQScalarParameter Q
      (actualBalanceGaussianArrayFlagSelectBySeed raw tape
        (actualBalanceGaussianRawFreeIndex_card_eq
            Q E U b raw tape htape c hc hmodel hsize hK) seed)
    actualBalanceGaussianRecurrencePolynomial coefficients = minpoly BinaryField k ∧
      Algebra.adjoin BinaryField ({k} : Set K) = ⊤ ∧
      LinearIndependent BinaryField (fun i : Fin s =>
        (actualBalanceGaussianArrayFlagSelectBySeed raw tape
          (actualBalanceGaussianRawFreeIndex_card_eq
              Q E U b raw tape htape c hc hmodel hsize hK) seed) ^ i.val) := by
  apply actualBalanceGaussianSampledScalar_primitive_of_filterPass Q
    candidate coefficients _
    (actualBalanceGaussianArrayFlagSelectBySeed_mem_qScalarRange
      Q E U b raw tape htape c hc hmodel hsize hK seed)
    hpass hK

end CorruptedFieldRecovery
