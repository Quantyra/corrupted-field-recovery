import CorruptedFieldRecovery.RawCandidateVerifierUniformBound
import CorruptedFieldRecovery.RawListRangeBitCost
import CorruptedFieldRecovery.RawRabinScanExecutableCost

/-! A logical live-space model for the verifier's outer control and list
storage. The model counts input bits, list-cell payloads, and recursive frames;
an explicit arithmetic-workspace parameter is left for the inner Nat
recurrences. This is not Lean heap or processor memory. -/

namespace CorruptedFieldRecovery

/-- Maximum active recursive frames in the actual short-circuit list scan.
The tail frame is included only when the current Rabin predicate succeeds. -/
def rawRabinCheckListPeakFrames (modulus : Nat) : List Nat → Nat
  | [] => 1
  | i :: is =>
      let step := rawRabinCheckIndexBitCosted modulus (i + 1)
      if step.1 then 1 + rawRabinCheckListPeakFrames modulus is else 1

theorem rawRabinCheckListPeakFrames_le {modulus : Nat} (indices : List Nat) :
    rawRabinCheckListPeakFrames modulus indices ≤ indices.length + 1 := by
  induction indices with
  | nil => simp [rawRabinCheckListPeakFrames]
  | cons i is ih =>
      simp only [rawRabinCheckListPeakFrames, List.length_cons]
      by_cases hstep : (rawRabinCheckIndexBitCosted modulus (i + 1)).1 = true
      · simp [hstep]
        omega
      · simp [hstep]

/-- In the owned append-based range builder, the old list and copied output
can be simultaneously live during a final append. This deliberately charges
both versions, regardless of runtime sharing or garbage-collection policy. -/
def rawListRangeCopyPeakCells (q : Nat) : Nat := 2 * q + 1

/-- The outer logical space envelope: input arrays, a conservative old/new
range-list overlap, range-builder frames, scan-list and short-circuit frames,
plus a parameter for live arithmetic workspace. `indexWidth` includes one
pointer/control bit per list entry. -/
def rawCandidateVerifierOuterPeakLiveBits {s : Nat}
    (candidate : RawFieldCandidate s) (arithmeticWorkspace : Nat) : Nat :=
  let q := s / 2
  let indexWidth := rawNatBitWidth q + 1
  candidate.modulus.size + candidate.scalar.size + arithmeticWorkspace +
    rawListRangeCopyPeakCells q * (indexWidth + 1) +
    (q + 1) * (indexWidth + 2) +
    q * (indexWidth + 1) + (q + 1) * (indexWidth + 2)

/-- Pair the exact composed verifier and declared charge with its logical
outer-space envelope. The arithmetic workspace remains an explicit input. -/
def rawCandidateVerifierSpaceModel {s : Nat}
    (candidate : RawFieldCandidate s) (arithmeticWorkspace : Nat) :
    Bool × Nat × Nat :=
  ((rawFieldCandidateFastCheckFullBitCosted candidate).1,
    ((rawFieldCandidateFastCheckFullBitCosted candidate).2,
      rawCandidateVerifierOuterPeakLiveBits candidate arithmeticWorkspace))

theorem rawCandidateVerifierSpaceModel_output {s : Nat}
    (candidate : RawFieldCandidate s) (arithmeticWorkspace : Nat) :
    (rawCandidateVerifierSpaceModel candidate arithmeticWorkspace).1 =
      rawFieldCandidateFastCheck candidate :=
  rawFieldCandidateFastCheckFullBitCosted_fst candidate

theorem rawCandidateVerifierSpaceModel_charge_bound {s : Nat}
    (candidate : RawFieldCandidate s) (arithmeticWorkspace : Nat) :
    (rawCandidateVerifierSpaceModel candidate arithmeticWorkspace).2.1 ≤
      2000000 *
        (s + candidate.modulus.size + candidate.scalar.size + 4) ^ 5 :=
  rawFieldCandidateFastCheckFullBitCosted_degree_five_bound candidate

/-- Each generated range index fits the payload width charged by the outer
space model. -/
theorem rawListRangeIndex_payload_width_le (q i : Nat)
    (hi : i ∈ (rawListRangeBitCosted q).1) :
    rawNatBitWidth i ≤ rawNatBitWidth q + 1 :=
  rawListRangeBitCosted_element_width_le q i hi

/-- The actual short-circuit evaluator never retains more scan frames than
the number of list entries plus its terminal frame. -/
theorem rawCandidateRabinScan_peak_frames_le {s : Nat}
    (candidate : RawFieldCandidate s) :
    rawRabinCheckListPeakFrames (rawFieldBitsToNat candidate.modulus)
      (List.range (s / 2)) ≤ s / 2 + 1 := by
  have h := rawRabinCheckListPeakFrames_le
    (modulus := rawFieldBitsToNat candidate.modulus) (List.range (s / 2))
  simpa using h

end CorruptedFieldRecovery
