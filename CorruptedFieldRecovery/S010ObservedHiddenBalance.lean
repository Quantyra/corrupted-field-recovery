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
space over `ZMod p`, using the derived `p = 2` coordinate casts. -/
def physicalEndomorphismToInput
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

/-- Pointwise formula for the derived physical-to-input endomorphism map. -/
theorem physicalEndomorphismToInput_apply
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

/-- The actual good tape's first three Q-images are the sampled clean frame
basis, and its fourth Q-image is the corresponding sampled vector. This uses
the tape event's actual `Q` correspondence, not an independently supplied
coordinate tuple. -/
theorem modeImage_actual_good_tape_q_frame_coordinates
    {K : Type*} [Field K] [Fintype K] [DecidableEq K] [Finite K]
    [CharP K 2] [Algebra BinaryField K] [FiniteDimensional BinaryField K]
    [Algebra (ZMod (ringChar K)) K]
    {s : Nat}
    (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K)
    (E : BinaryTensor (3 * s))
    (U : Submodule BinaryField (KTriple K))
    (b : (Fin 4 → FieldTriple K) → Module.Basis (Fin s) BinaryField K)
    (tape : FiveWordTape s)
    (htape : tape ∈ actualFiveGoodTapeSet K Q
      (modeImageSemanticCleanFieldSet Q E) U b) :
    ∃ fr : Σ _xy : (Σ _x : FieldTriple K, FieldTriple K), FieldTriple K,
      ∃ v : FieldTriple K,
        fr ∈ cleanFrameSet (K := K) (modeImageSemanticCleanFieldSet Q E) ∧
        v ∈ goodFourthFinset K (modeImageSemanticCleanFieldSet Q E)
          (nonGenerators K) fr ∧
        (fun i => Q (tape.1 i)) = canonicalGoodFourFlatTuple K ⟨fr, v⟩ ∧
        (∀ i : Fin 3,
          Q (tape.1 i.castSucc) =
            canonicalGoodFrameBasis K (modeImageSemanticCleanFieldSet Q E) fr i) ∧
        Q (tape.1 3) = v := by
  rcases modeImage_actual_good_tape_four_contraction_identification
      Q E U b tape htape (1 : K) one_ne_zero with
    ⟨fr, v, hfr, hv, hflat, _⟩
  let A := modeImageSemanticCleanFieldSet Q E
  let B := canonicalGoodFrameBasis K A fr
  have hB0 : B 0 = fr.1.1 := by
    change canonicalGoodFrameBasis K A fr 0 = fr.1.1
    rw [canonicalGoodFrameBasis_eq_cleanBasisTripleBasis K A fr hfr]
    simp [cleanBasisTripleBasis, cleanBasisTripleVectors]
    rfl
  have hB1 : B 1 = fr.1.2 := by
    change canonicalGoodFrameBasis K A fr 1 = fr.1.2
    rw [canonicalGoodFrameBasis_eq_cleanBasisTripleBasis K A fr hfr]
    simp [cleanBasisTripleBasis, cleanBasisTripleVectors]
    rfl
  have hB2 : B 2 = fr.2 := by
    change canonicalGoodFrameBasis K A fr 2 = fr.2
    rw [canonicalGoodFrameBasis_eq_cleanBasisTripleBasis K A fr hfr]
    simp [cleanBasisTripleBasis, cleanBasisTripleVectors]
    rfl
  have hq0 : Q (tape.1 0) = B 0 := by
    have h := congrFun hflat 0
    change Q (tape.1 0) = canonicalGoodFourFlatTuple K ⟨fr, v⟩ 0 at h
    simpa [canonicalGoodFourFlatTuple, B, A] using h.trans hB0.symm
  have hq1 : Q (tape.1 1) = B 1 := by
    have h := congrFun hflat 1
    change Q (tape.1 1) = canonicalGoodFourFlatTuple K ⟨fr, v⟩ 1 at h
    simpa [canonicalGoodFourFlatTuple, B, A] using h.trans hB1.symm
  have hq2 : Q (tape.1 2) = B 2 := by
    have h := congrFun hflat 2
    change Q (tape.1 2) = canonicalGoodFourFlatTuple K ⟨fr, v⟩ 2 at h
    simpa [canonicalGoodFourFlatTuple, B, A] using h.trans hB2.symm
  have hq3 : Q (tape.1 3) = v := by
    have h := congrFun hflat 3
    change Q (tape.1 3) = canonicalGoodFourFlatTuple K ⟨fr, v⟩ 3 at h
    simpa [canonicalGoodFourFlatTuple] using h
  refine ⟨fr, v, hfr, hv, hflat, ?_, ?_⟩
  · intro i
    fin_cases i
    · simpa [B] using hq0
    · simpa [B] using hq1
    · simpa [B] using hq2
  · exact hq3

end

end CorruptedFieldRecovery
