import CorruptedFieldRecovery.S010BalanceGaussianRawKernelBasis
import CorruptedFieldRecovery.S010BalanceGaussianArrayFlagExecutionTrace

namespace CorruptedFieldRecovery

/-- Candidate endomorphisms built from the matrix view and pivot transcript
returned by the instrumented nested-array scan. The transcript and free-column
complement are computed from that run; they are not supplied separately. -/
def actualBalanceGaussianArrayFlagCandidateEndList {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s) :
    List (Module.End (ZMod 2) (BinaryVector (3 * s))) :=
  let run := actualBalanceGaussianSerializedArrayFlagScanInstrumented raw tape
  let matrix := actualBalanceGaussianArrayView run.1.1.1
  let pivots := run.1.2
  let freeColumns :=
    (List.ofFn fun column : Fin ((3 * s) * (3 * s)) => column).filter
      (fun column => decide (column ∉ pivots.map Prod.snd))
  freeColumns.map fun free =>
    actualBalanceGaussianEndFromCoordinates
      (balanceGaussianFreeKernelCandidate matrix pivots free)

/-- Refinement identifies the instrumented array run's free-column candidate
list with the already-proved raw Fin-matrix candidate list. -/
theorem actualBalanceGaussianArrayFlagCandidateEndList_eq_raw {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s) :
    actualBalanceGaussianArrayFlagCandidateEndList raw tape =
      actualBalanceGaussianRawCandidateEndList raw tape := by
  let run := actualBalanceGaussianSerializedArrayFlagScanInstrumented raw tape
  have href := actualBalanceGaussianSerializedArrayFlagScanInstrumented_refines
    raw tape
  have hmatrix : actualBalanceGaussianArrayView run.1.1.1 =
      (actualBalanceGaussianRawScan raw tape).1 := congrArg Prod.fst href
  have hpivots : run.1.2 =
      (actualBalanceGaussianRawScan raw tape).2 := congrArg Prod.snd href
  unfold actualBalanceGaussianArrayFlagCandidateEndList
    actualBalanceGaussianRawCandidateEndList
    actualBalanceGaussianRawFreeColumns
  simp only [run] at hmatrix hpivots
  dsimp only
  rw [← hmatrix, ← hpivots]

/-- Every endomorphism emitted from the actual instrumented array run obeys
the physical four-slot balance equations on the decoded raw input. -/
theorem actualBalanceGaussianArrayFlagCandidateEndList_balanced {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s)
    {T : Module.End (ZMod 2) (BinaryVector (3 * s))}
    (hT : T ∈ actualBalanceGaussianArrayFlagCandidateEndList raw tape) :
    actualFourBilinearBalanced (decodeRawArray (n := 3 * s) raw) tape T := by
  rw [actualBalanceGaussianArrayFlagCandidateEndList_eq_raw] at hT
  exact actualBalanceGaussianRawCandidateEndList_balanced raw tape hT

/-- Under the declared raw-array length condition, every emitted candidate
passes the actual finite balance checker. This is soundness for the returned
list; it does not claim that the list is nonempty or that a selected candidate
equals the manuscript's recovery constructor. -/
theorem actualBalanceGaussianArrayFlagCandidateEndList_checker_true {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s)
    (hsize : raw.size = (3 * s) * (3 * s) * (3 * s))
    {T : Module.End (ZMod 2) (BinaryVector (3 * s))}
    (hT : T ∈ actualBalanceGaussianArrayFlagCandidateEndList raw tape) :
    actualBalanceRawInputConstraintCheck raw tape T = true := by
  apply (actualBalanceRawInputConstraintCheck_iff raw tape T).2
  exact ⟨hsize,
    actualBalanceGaussianArrayFlagCandidateEndList_balanced raw tape hT⟩

/-- With an explicit nonemptiness premise, every member of the instrumented
candidate list is checker-accepted. The premise is intentionally not derived
from the desired recovery conclusion. -/
theorem actualBalanceGaussianArrayFlagCandidateList_nonempty_sound {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s)
    (hsize : raw.size = (3 * s) * (3 * s) * (3 * s))
    (_hnonempty : actualBalanceGaussianArrayFlagCandidateEndList raw tape ≠ []) :
    ∀ T ∈ actualBalanceGaussianArrayFlagCandidateEndList raw tape,
      actualBalanceRawInputConstraintCheck raw tape T = true := by
  intro T hT
  exact actualBalanceGaussianArrayFlagCandidateEndList_checker_true
    raw tape hsize hT

end CorruptedFieldRecovery