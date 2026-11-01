import CorruptedFieldRecovery.S010BalanceGaussianArrayFlagKernelOutputBridge
import CorruptedFieldRecovery.S010ObservedHiddenBalance

namespace CorruptedFieldRecovery

/-- A nonzero balanced endomorphism forces the deterministic raw Gaussian scan
to have at least one free-column candidate. The proof uses the scan's full
reconstruction theorem: an empty free-column index would reconstruct every
balanced endomorphism as the zero sum. -/
theorem actualBalanceGaussianRawCandidateEndList_nonempty_of_nonzero_balanced
    {s : Nat} (raw : RawCoefficientArray) (tape : FiveWordTape s)
    (T : Module.End (ZMod 2) (BinaryVector (3 * s)))
    (hbalanced : actualFourBilinearBalanced
      (decodeRawArray (n := 3 * s) raw) tape T)
    (hT : T ≠ 0) :
    actualBalanceGaussianRawCandidateEndList raw tape ≠ [] := by
  classical
  intro hlist
  have hcolumns : actualBalanceGaussianRawFreeColumns raw tape = [] := by
    simpa [actualBalanceGaussianRawCandidateEndList] using hlist
  let pivots := (actualBalanceGaussianRawScan raw tape).2
  let freeIndex := balanceGaussianFreeIndex pivots
  have hempty : IsEmpty freeIndex := by
    refine ⟨fun free => ?_⟩
    have hmem : free.1 ∈ actualBalanceGaussianRawFreeColumns raw tape := by
      refine List.mem_filter.mpr ⟨List.mem_ofFn.mpr ⟨free.1, rfl⟩, ?_⟩
      simpa [pivots] using free.2
    rw [hcolumns] at hmem
    simp at hmem
  letI : IsEmpty freeIndex := hempty
  have hsum :
      (∑ free : freeIndex,
        actualBalanceGaussianInputCoordinates T free.1 •
          actualBalanceGaussianRawCandidateFamily raw tape free) = 0 := by
    simp
  have hrec := actualBalanceGaussianRawBalanced_endomorphism_reconstruct
    raw tape T hbalanced
  rw [hsum] at hrec
  exact hT hrec

/-- Under an actual good tape and the explicit observed trace-determinant model
promise with nonzero scalar coefficient, the raw array solver's candidate list
is nonempty. The witness is the Q-conjugate of scalar one, whose balance
follows from the good-event characterization; nonemptiness is then derived by
full-scan reconstruction, not assumed. -/
theorem actualBalanceGaussianArrayFlagCandidateEndList_nonempty_of_good_model
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
      (decodeRawArray (n := 3 * s) raw) E LinearMap.id Q c) :
    actualBalanceGaussianArrayFlagCandidateEndList raw tape ≠ [] := by
  let T : Module.End BinaryField (BinaryVector (3 * s)) :=
    qScalarConjugateLinearMap Q (1 : K)
  have hiff := actual_good_tape_observed_balance_iff_mem_qScalarConjugateEndRange
    Q E U b tape htape (decodeRawArray (n := 3 * s) raw) c hmodel hc
  have hTbalanced :
      actualFourBilinearBalanced (decodeRawArray (n := 3 * s) raw) tape T := by
    apply (hiff T).mpr
    exact ⟨1, rfl⟩
  have hTne : T ≠ 0 := by
    intro hzero
    have hmap : qScalarConjugateLinearMap Q (1 : K) =
        qScalarConjugateLinearMap Q 0 := by
      simp [T, hzero]
    have hone : (1 : K) = 0 := qScalarConjugateLinearMap_injective Q hmap
    exact one_ne_zero hone
  have hraw : actualBalanceGaussianRawCandidateEndList raw tape ≠ [] :=
    actualBalanceGaussianRawCandidateEndList_nonempty_of_nonzero_balanced
      raw tape T (by simpa [T, BinaryField] using hTbalanced) (by
        simpa [T, BinaryField] using hTne)
  rw [actualBalanceGaussianArrayFlagCandidateEndList_eq_raw raw tape]
  exact hraw

/-- Deterministic first-candidate selector on the list emitted by the
instrumented array run. It returns `none` exactly when the computed list is
empty. -/
def actualBalanceGaussianArrayFlagSelectFirst {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s) :
    Option (Module.End (ZMod 2) (BinaryVector (3 * s))) :=
  (actualBalanceGaussianArrayFlagCandidateEndList raw tape).head?

/-- Under the same good-tape/model assumptions, the first-candidate selector
returns some endomorphism. This establishes existence of a computed candidate
without identifying it with a manuscript recovery routine. -/
theorem actualBalanceGaussianArrayFlagSelectFirst_isSome_of_good_model
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
      (decodeRawArray (n := 3 * s) raw) E LinearMap.id Q c) :
    actualBalanceGaussianArrayFlagSelectFirst raw tape ≠ none := by
  have hne := actualBalanceGaussianArrayFlagCandidateEndList_nonempty_of_good_model
    Q E U b raw tape htape c hc hmodel
  cases hlist : actualBalanceGaussianArrayFlagCandidateEndList raw tape with
  | nil => simp [hlist] at hne
  | cons head tail => simp [actualBalanceGaussianArrayFlagSelectFirst, hlist]

/-- If the dense raw-array length condition holds, the selected first
candidate passes the finite balance checker whenever the selector returns it. -/
theorem actualBalanceGaussianArrayFlagSelectFirst_checker_true
    {s : Nat} (raw : RawCoefficientArray) (tape : FiveWordTape s)
    (hsize : raw.size = (3 * s) * (3 * s) * (3 * s))
    {T : Module.End (ZMod 2) (BinaryVector (3 * s))}
    (hselected : actualBalanceGaussianArrayFlagSelectFirst raw tape = some T) :
    actualBalanceRawInputConstraintCheck raw tape T = true := by
  cases hlist : actualBalanceGaussianArrayFlagCandidateEndList raw tape with
  | nil => simp [actualBalanceGaussianArrayFlagSelectFirst, hlist] at hselected
  | cons head tail =>
    simp [actualBalanceGaussianArrayFlagSelectFirst, hlist] at hselected
    subst T
    apply actualBalanceGaussianArrayFlagCandidateEndList_checker_true
      raw tape hsize
    simp [hlist]

end CorruptedFieldRecovery