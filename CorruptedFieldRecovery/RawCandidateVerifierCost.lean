import CorruptedFieldRecovery.RawCandidateShapeCost
import CorruptedFieldRecovery.RawListRangeBitCost
import CorruptedFieldRecovery.RawRabinScanExecutableCost

/-! Compose the measured shape gate, explicit range builder, and
short-circuit Rabin scan into one executable cost model. -/

namespace CorruptedFieldRecovery

/-- The actual raw decoder has quadratic declared shift/add charge in the
number of input bits. -/
theorem rawBitsToNatBitCosted_cost_le (bits : List Bool) :
    (rawBitsToNatBitCosted bits).2 ≤ bits.length * (bits.length + 2) := by
  induction bits with
  | nil => simp [rawBitsToNatBitCosted]
  | cons bit tail ih =>
      have hvalue := rawBitsToNat_lt_pow_length tail
      have hwidth : rawNatBitWidth (rawBitsToNat tail) ≤ tail.length + 1 := by
        by_cases hzero : rawBitsToNat tail = 0
        · simp [rawNatBitWidth, hzero]
        · have hpositive : 0 < tail.length := by
            cases tail with
            | nil => simp [rawBitsToNat] at hzero
            | cons head rest => simp
          have hlog := rawLog2_lt_of_lt_pow hpositive hvalue
          unfold rawNatBitWidth
          omega
      simp only [rawBitsToNatBitCosted, List.length_cons]
      have hfst := rawBitsToNatBitCosted_fst tail
      rw [hfst]
      nlinarith [ih, hwidth]

/-- Array decoding includes the exact recursive decoder and one declared
list-cell conversion visit per input bit. -/
theorem rawFieldBitsToNatBitCosted_cost_le (bits : RawFieldBits) :
    (rawFieldBitsToNatBitCosted bits).2 ≤ bits.size * (bits.size + 3) := by
  have h := rawBitsToNatBitCosted_cost_le bits.toList
  have hlen : bits.toList.length = bits.size := by simp
  rw [hlen] at h
  change (rawBitsToNatBitCosted bits.toList).2 + bits.size ≤ _
  nlinarith [h]

/-- Full executable candidate gate, charging the shape checks first and
constructing the degree list only when shape succeeds. The custom range
recurrence is the implementation whose cost is charged here; this theorem
does not assign a cost to Lean's library `List.range`. -/
def rawFieldCandidateFastCheckFullBitCosted {s : Nat}
    (candidate : RawFieldCandidate s) : Bool × Nat :=
  let shape := rawFieldCandidateShapeCheckBitCosted candidate
  if shape.1 then
    let indices := rawListRangeBitCosted (s / 2)
    let scan := rawRabinCheckListBitCosted
      (rawFieldBitsToNat candidate.modulus) indices.1
    (scan.1, shape.2 + indices.2 + scan.2)
  else (false, shape.2)

/-- The composed costed execution returns exactly the accepted hfield-free
fast Boolean verifier. -/
theorem rawFieldCandidateFastCheckFullBitCosted_fst {s : Nat}
    (candidate : RawFieldCandidate s) :
    (rawFieldCandidateFastCheckFullBitCosted candidate).1 =
      rawFieldCandidateFastCheck candidate := by
  by_cases hshape : rawFieldCandidateShapeCheck candidate = true
  · have hshape' : (rawFieldCandidateShapeCheckBitCosted candidate).1 = true := by
      rw [rawFieldCandidateShapeCheckBitCosted_fst]
      exact hshape
    simp [rawFieldCandidateFastCheckFullBitCosted, hshape, hshape',
      rawListRangeBitCosted_fst, rawRabinCheckListBitCosted_fst,
      rawFieldCandidateFastCheck, rawCandidateRabinCheck,
      rawCandidateFrobenius]
    rfl
  · have hshape' : (rawFieldCandidateShapeCheckBitCosted candidate).1 = false := by
      rw [rawFieldCandidateShapeCheckBitCosted_fst]
      cases h : rawFieldCandidateShapeCheck candidate <;> simp_all
    simp [rawFieldCandidateFastCheckFullBitCosted, hshape, hshape',
      rawFieldCandidateFastCheck]

/-- Under successful shape checks, the full declared charge is at most the
shape gate charge plus explicit range construction and short-circuit scan
charges. -/
theorem rawFieldCandidateFastCheckFullBitCosted_cost_le {s : Nat}
    (candidate : RawFieldCandidate s)
    (hshape : rawFieldCandidateShapeCheck candidate = true) :
    (rawFieldCandidateFastCheckFullBitCosted candidate).2 ≤
      (rawFieldCandidateShapeCheckBitCosted candidate).2 + (s / 2) ^ 2 +
        (s / 2) * rawRabinScanUniformCharge (s + 1) (s / 2) := by
  have hrange := rawListRangeBitCosted_cost_le (s / 2)
  have hscan :
      (rawRabinCheckListBitCosted (rawFieldBitsToNat candidate.modulus)
        (rawListRangeBitCosted (s / 2)).1).2 ≤
      (s / 2) * rawRabinScanUniformCharge (s + 1) (s / 2) := by
    rw [rawListRangeBitCosted_fst]
    simpa [rawCandidateRabinCheckBitCosted] using
      rawCandidateRabinCheckBitCosted_cost_le candidate hshape
  have hshape' : (rawFieldCandidateShapeCheckBitCosted candidate).1 = true := by
    rw [rawFieldCandidateShapeCheckBitCosted_fst]
    exact hshape
  simp only [rawFieldCandidateFastCheckFullBitCosted, hshape', ↓reduceIte]
  calc
    _ ≤ (rawFieldCandidateShapeCheckBitCosted candidate).2 +
        (s / 2) * (s / 2) +
        (s / 2) * rawRabinScanUniformCharge (s + 1) (s / 2) := by
          omega
    _ = (rawFieldCandidateShapeCheckBitCosted candidate).2 +
        (s / 2) ^ 2 +
        (s / 2) * rawRabinScanUniformCharge (s + 1) (s / 2) := by
          simp [pow_two]

end CorruptedFieldRecovery
