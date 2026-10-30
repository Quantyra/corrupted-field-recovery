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

private def binaryScalarToIndex {p : Nat} (hp : p = 2) : ZMod 2 ≃ ZMod p :=
  Equiv.cast (congrArg ZMod hp.symm)

private theorem trace_binary_cast_eq_index
    {p : Nat} (K : Type*) [Field K] [Finite K]
    [algBinary : Algebra BinaryField K] [algIndex : Algebra (ZMod p) K]
    (hp : p = 2) (x : K) :
    binaryScalarToIndex hp (Algebra.trace BinaryField K x) =
      Algebra.trace (ZMod p) K x := by
  cases hp
  have hAlg : algBinary = algIndex := Subsingleton.elim _ _
  cases hAlg
  simp [binaryScalarToIndex]

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

private theorem qCleanSampleOnSlot
    {K : Type*} [Field K] [Finite K] [Algebra BinaryField K]
    [CharP K 2] [Algebra (ZMod (ringChar K)) K]
    {s : Nat} (Q : BinaryVector (3 * s) ≃ₗ[BinaryField] FieldTriple K)
    (c : K) (z : BinaryVector (3 * s)) (slot : FieldTriple K)
    (hz : Q z = slot)
    (x y : BinaryVector (3 * s))
    (xi yi : BinaryInput K (3 * s))
    (hxi : modeImage_inputEquiv_from_Q Q xi = Q x)
    (hyi : modeImage_inputEquiv_from_Q Q yi = Q y) :
    binaryScalarToIndex (ringChar.eq K 2)
      (physicalThirdSlotBilinForm (qTraceDeterminantTensor Q c) z x y) =
      Algebra.trace (ZMod (ringChar K)) K
        (c * fieldDet3 (modeImage_inputEquiv_from_Q Q xi)
          (modeImage_inputEquiv_from_Q Q yi) slot) := by
  change binaryScalarToIndex (ringChar.eq K 2)
      (Algebra.trace BinaryField K
        (c * fieldDet3 (Q x) (Q y) (Q z))) = _
  rw [← hxi, ← hyi, hz]
  exact trace_binary_cast_eq_index K (ringChar.eq K 2)
    (c * fieldDet3 (modeImage_inputEquiv_from_Q Q xi)
      (modeImage_inputEquiv_from_Q Q yi) slot)

/-- The actual good-tape physical four-balance equations for the Q-derived
clean tensor are equivalent to the manuscript's hidden sampled four equations.
The input equivalence and endomorphism are both derived from Q and the
characteristic-two coordinate cast; the sampled frame and fourth vector are
extracted from this same actual tape. -/
theorem actual_good_tape_clean_balance_iff_hidden
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
      (modeImageSemanticCleanFieldSet Q E) U b)
    (c : K) (T : Module.End (ZMod 2) (BinaryVector (3 * s))) :
    actualFourBilinearBalanced (qTraceDeterminantTensor Q c) tape T ↔
      hiddenFourBalanced K (modeImage_inputEquiv_from_Q Q)
        (canonicalGoodFrameBasis K (modeImageSemanticCleanFieldSet Q E)
          ((modeImage_actual_good_tape_q_frame_coordinates
            Q E U b tape htape).choose))
        ((modeImage_actual_good_tape_q_frame_coordinates
          Q E U b tape htape).choose_spec.choose)
        c (physicalEndomorphismToInput (ringChar.eq K 2) T) := by
  let hcoords := modeImage_actual_good_tape_q_frame_coordinates Q E U b tape htape
  let fr := hcoords.choose
  let frameData := hcoords.choose_spec
  let v := frameData.choose
  rcases frameData.choose_spec with ⟨hfr, hv, hflat, hslots, hslot3⟩
  let A := modeImageSemanticCleanFieldSet Q E
  let B := canonicalGoodFrameBasis K A fr
  let iota := modeImage_inputEquiv_from_Q Q
  let hp := ringChar.eq K 2
  let Tin := physicalEndomorphismToInput hp T
  have hinput (x : BinaryInput K (3 * s)) : iota x = Q (modeImage_inputVectorToBinary x) := by
    simpa [iota] using modeImage_inputEquiv_from_Q_apply Q x
  have hinputT (x : BinaryInput K (3 * s)) :
      iota (Tin x) = Q (T (modeImage_inputVectorToBinary x)) := by
    simpa [iota, Tin, hp] using
      modeImage_inputEquiv_from_Q_transport_endomorphism Q T x
  have hback (x : BinaryVector (3 * s)) :
      iota (binaryToInputCast hp x) = Q x := by
    rw [hinput]
    change Q (inputToBinaryCast hp (binaryToInputCast hp x)) = Q x
    rw [inputCast_binaryCast_cancel]
  have hbackT (x : BinaryVector (3 * s)) :
      iota (Tin (binaryToInputCast hp x)) = Q (T x) := by
    calc
      iota (Tin (binaryToInputCast hp x)) =
          Q (T (modeImage_inputVectorToBinary (K := K) (binaryToInputCast hp x))) :=
        hinputT _
      _ = Q (T x) := congrArg Q (congrArg T (inputCast_binaryCast_cancel hp x))
  have hs0 : Q (tape.1 0) = B 0 := by
    change Q (tape.1 0) = canonicalGoodFrameBasis K A fr 0
    exact hslots 0
  have hs1 : Q (tape.1 1) = B 1 := by
    change Q (tape.1 1) = canonicalGoodFrameBasis K A fr 1
    exact hslots 1
  have hs2 : Q (tape.1 2) = B 2 := by
    change Q (tape.1 2) = canonicalGoodFrameBasis K A fr 2
    exact hslots 2
  have hs3 : Q (tape.1 3) = v := hslot3
  change (∀ i : Fin 4, ∀ x y : BinaryVector (3 * s),
      physicalThirdSlotBilinForm (qTraceDeterminantTensor Q c)
        (tape.1 i) (T x) y =
      physicalThirdSlotBilinForm (qTraceDeterminantTensor Q c)
        (tape.1 i) x (T y)) ↔ _
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x y
      have hleft := qCleanSampleOnSlot Q c (tape.1 0) (B 0) hs0
        (T (modeImage_inputVectorToBinary x)) (modeImage_inputVectorToBinary y)
        (Tin x) y (hinputT x) (hinput y)
      have hright := qCleanSampleOnSlot Q c (tape.1 0) (B 0) hs0
        (modeImage_inputVectorToBinary x) (T (modeImage_inputVectorToBinary y))
        x (Tin y) (hinput x) (hinputT y)
      have hh := h 0 (modeImage_inputVectorToBinary x)
        (modeImage_inputVectorToBinary y)
      have hhc := congrArg (binaryScalarToIndex hp) hh
      rw [hleft, hright] at hhc
      simpa [iota, Tin, sampledContraction0, hcoords, fr, frameData, v, A, B] using hhc
    · intro x y
      have hleft := qCleanSampleOnSlot Q c (tape.1 1) (B 1) hs1
        (T (modeImage_inputVectorToBinary x)) (modeImage_inputVectorToBinary y)
        (Tin x) y (hinputT x) (hinput y)
      have hright := qCleanSampleOnSlot Q c (tape.1 1) (B 1) hs1
        (modeImage_inputVectorToBinary x) (T (modeImage_inputVectorToBinary y))
        x (Tin y) (hinput x) (hinputT y)
      have hh := h 1 (modeImage_inputVectorToBinary x)
        (modeImage_inputVectorToBinary y)
      have hhc := congrArg (binaryScalarToIndex hp) hh
      rw [hleft, hright] at hhc
      simpa [iota, Tin, sampledContraction1, hcoords, fr, frameData, v, A, B] using hhc
    · intro x y
      have hleft := qCleanSampleOnSlot Q c (tape.1 2) (B 2) hs2
        (T (modeImage_inputVectorToBinary x)) (modeImage_inputVectorToBinary y)
        (Tin x) y (hinputT x) (hinput y)
      have hright := qCleanSampleOnSlot Q c (tape.1 2) (B 2) hs2
        (modeImage_inputVectorToBinary x) (T (modeImage_inputVectorToBinary y))
        x (Tin y) (hinput x) (hinputT y)
      have hh := h 2 (modeImage_inputVectorToBinary x)
        (modeImage_inputVectorToBinary y)
      have hhc := congrArg (binaryScalarToIndex hp) hh
      rw [hleft, hright] at hhc
      simpa [iota, Tin, sampledContraction2, hcoords, fr, frameData, v, A, B] using hhc
    · intro x y
      have hleft := qCleanSampleOnSlot Q c (tape.1 3) v hs3
        (T (modeImage_inputVectorToBinary x)) (modeImage_inputVectorToBinary y)
        (Tin x) y (hinputT x) (hinput y)
      have hright := qCleanSampleOnSlot Q c (tape.1 3) v hs3
        (modeImage_inputVectorToBinary x) (T (modeImage_inputVectorToBinary y))
        x (Tin y) (hinput x) (hinputT y)
      have hh := h 3 (modeImage_inputVectorToBinary x)
        (modeImage_inputVectorToBinary y)
      have hhc := congrArg (binaryScalarToIndex hp) hh
      rw [hleft, hright] at hhc
      simpa [iota, Tin, sampledContraction4, hcoords, fr, frameData, v, A, B] using hhc
  · rintro ⟨h0, h1, h2, h4⟩ i x y
    fin_cases i
    · let xi := binaryToInputCast hp x
      let yi := binaryToInputCast hp y
      have hleft := qCleanSampleOnSlot Q c (tape.1 0) (B 0) hs0
        (T x) y (Tin xi) yi (hbackT x) (hback y)
      have hright := qCleanSampleOnSlot Q c (tape.1 0) (B 0) hs0
        x (T y) xi (Tin yi) (hback x) (hbackT y)
      have hh := h0 xi yi
      apply (binaryScalarToIndex hp).injective
      calc
        _ = Algebra.trace (ZMod (ringChar K)) K
            (c * fieldDet3 (iota (Tin xi)) (iota yi) (B 0)) := by simpa using hleft
        _ = Algebra.trace (ZMod (ringChar K)) K
            (c * fieldDet3 (iota xi) (iota (Tin yi)) (B 0)) := by
              simpa [iota, Tin, sampledContraction0, hcoords, fr, frameData, v, A, B] using hh
        _ = _ := by simpa using hright.symm
    · let xi := binaryToInputCast hp x
      let yi := binaryToInputCast hp y
      have hleft := qCleanSampleOnSlot Q c (tape.1 1) (B 1) hs1
        (T x) y (Tin xi) yi (hbackT x) (hback y)
      have hright := qCleanSampleOnSlot Q c (tape.1 1) (B 1) hs1
        x (T y) xi (Tin yi) (hback x) (hbackT y)
      have hh := h1 xi yi
      apply (binaryScalarToIndex hp).injective
      calc
        _ = Algebra.trace (ZMod (ringChar K)) K
            (c * fieldDet3 (iota (Tin xi)) (iota yi) (B 1)) := by simpa using hleft
        _ = Algebra.trace (ZMod (ringChar K)) K
            (c * fieldDet3 (iota xi) (iota (Tin yi)) (B 1)) := by
              simpa [iota, Tin, sampledContraction1, hcoords, fr, frameData, v, A, B] using hh
        _ = _ := by simpa using hright.symm
    · let xi := binaryToInputCast hp x
      let yi := binaryToInputCast hp y
      have hleft := qCleanSampleOnSlot Q c (tape.1 2) (B 2) hs2
        (T x) y (Tin xi) yi (hbackT x) (hback y)
      have hright := qCleanSampleOnSlot Q c (tape.1 2) (B 2) hs2
        x (T y) xi (Tin yi) (hback x) (hbackT y)
      have hh := h2 xi yi
      apply (binaryScalarToIndex hp).injective
      calc
        _ = Algebra.trace (ZMod (ringChar K)) K
            (c * fieldDet3 (iota (Tin xi)) (iota yi) (B 2)) := by simpa using hleft
        _ = Algebra.trace (ZMod (ringChar K)) K
            (c * fieldDet3 (iota xi) (iota (Tin yi)) (B 2)) := by
              simpa [iota, Tin, sampledContraction2, hcoords, fr, frameData, v, A, B] using hh
        _ = _ := by simpa using hright.symm
    · let xi := binaryToInputCast hp x
      let yi := binaryToInputCast hp y
      have hleft := qCleanSampleOnSlot Q c (tape.1 3) v hs3
        (T x) y (Tin xi) yi (hbackT x) (hback y)
      have hright := qCleanSampleOnSlot Q c (tape.1 3) v hs3
        x (T y) xi (Tin yi) (hback x) (hbackT y)
      have hh := h4 xi yi
      apply (binaryScalarToIndex hp).injective
      calc
        _ = Algebra.trace (ZMod (ringChar K)) K
            (c * fieldDet3 (iota (Tin xi)) (iota yi) v) := by simpa using hleft
        _ = Algebra.trace (ZMod (ringChar K)) K
            (c * fieldDet3 (iota xi) (iota (Tin yi)) v) := by
              simpa [iota, Tin, sampledContraction4, hcoords, fr, frameData, v, A, B] using hh
        _ = _ := by simpa using hright.symm

end

end CorruptedFieldRecovery
