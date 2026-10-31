import CorruptedFieldRecovery.RawBinaryWordXor

/-! Bit-list control primitives for one fuel-bounded reducer iteration.
The threshold predicate scans a low-endian word for any set bit at or above
the requested degree. The leading-one scan returns the highest set-bit index.
Together with word XOR and a low-end zero shift, they refine one cancellation
step. This remains a functional bit-list model: list traversal, allocation,
conversion, control storage, and total live space are not yet charged. -/

namespace CorruptedFieldRecovery

/-- Decide whether all word bits at positions `degree` and above are zero. -/
def rawBinaryWordBelowPowTwo (degree : Nat) : List Bool → Bool
  | [] => true
  | bit :: tail =>
      match degree with
      | 0 => (!bit) && rawBinaryWordBelowPowTwo 0 tail
      | degree + 1 => rawBinaryWordBelowPowTwo degree tail

/-- The bit scan exactly decides whether the decoded mask is below `2^degree`.
This holds for words with or without high zero padding. -/
theorem rawBinaryWordBelowPowTwo_spec (degree : Nat) (word : List Bool) :
    rawBinaryWordBelowPowTwo degree word =
      decide (rawBitsToNat word < 2 ^ degree) := by
  induction word generalizing degree with
  | nil => simp [rawBinaryWordBelowPowTwo, rawBitsToNat]
  | cons bit tail ih =>
      cases degree with
      | zero =>
          cases bit <;>
            simp [rawBinaryWordBelowPowTwo, rawBitsToNat, ih]
      | succ degree =>
          have hshift (b : Bool) (n : Nat) :
              (if b then 1 else 0) + 2 * n < 2 ^ (degree + 1) ↔
                n < 2 ^ degree := by
            rw [pow_succ]
            cases b <;> simp <;> omega
          simp [rawBinaryWordBelowPowTwo, rawBitsToNat, ih, hshift]

/-- Scan a little-endian word and return the highest set-bit index, or `none`
for the all-zero word. -/
def rawBinaryWordLeadingOne : List Bool → Option Nat
  | [] => none
  | bit :: tail =>
      match rawBinaryWordLeadingOne tail with
      | some index => some (index + 1)
      | none => if bit then some 0 else none

/-- The leading-one scan returns `none` on every word decoding to zero,
including arbitrary trailing zero padding. -/
theorem rawBinaryWordLeadingOne_eq_none_of_zero (word : List Bool)
    (hzero : rawBitsToNat word = 0) :
    rawBinaryWordLeadingOne word = none := by
  induction word with
  | nil => rfl
  | cons bit tail ih =>
      cases bit with
      | true => simp [rawBitsToNat] at hzero
      | false =>
          have htail : rawBitsToNat tail = 0 := by
            simpa [rawBitsToNat] using hzero
          simp [rawBinaryWordLeadingOne, ih htail]

/-- On any nonzero word, the leading-one scan returns exactly the `Nat.log2`
of its decoded value. -/
theorem rawBinaryWordLeadingOne_spec (word : List Bool)
    (hne : rawBitsToNat word ≠ 0) :
    rawBinaryWordLeadingOne word = some (Nat.log2 (rawBitsToNat word)) := by
  induction word with
  | nil => simp [rawBitsToNat] at hne
  | cons bit tail ih =>
      by_cases htail : rawBitsToNat tail = 0
      · have hnone := rawBinaryWordLeadingOne_eq_none_of_zero tail htail
        have hlog1 : Nat.log2 1 = 0 := by
          rw [Nat.log2_eq_log_two]
          simp
        cases bit
        · simp [rawBitsToNat, htail] at hne
        · simp [rawBinaryWordLeadingOne, rawBitsToNat, htail, hnone, hlog1]
      · have hrec := ih htail
        have hvalue : rawBitsToNat (bit :: tail) =
            Nat.bit bit (rawBitsToNat tail) := rawBitsToNat_cons bit tail
        have hshift : (Nat.bit bit (rawBitsToNat tail)) >>> 1 ≠ 0 := by
          simpa using htail
        have hlog : Nat.log2 (rawBitsToNat (bit :: tail)) =
            Nat.log2 (rawBitsToNat tail) + 1 := by
          rw [hvalue, Nat.log2_eq_succ_log2_shiftRight hshift]
          simp
        simp [rawBinaryWordLeadingOne, hrec, hlog]

/-- A reducer cancellation over bit-list states. The only Nat-level value
used to select the shift is the leading-index result computed by the bit
scan; the shifted modulus and XOR are both word operations. -/
def rawReduceStepWordFromBits
    (modulusWord : List Bool) (degree : Nat) (currentWord : List Bool) :
    List Bool :=
  rawBinaryWordXor currentWord
    (rawBinaryWordShiftLeft
      ((rawBinaryWordLeadingOne currentWord).getD 0 - degree)
      modulusWord)

/-- Whenever reduction is active, the word-state cancellation decodes to the
exact existing Nat-mask reducer step. The active premise guarantees a
nonzero current mask, so the leading-bit scan has a real result. -/
theorem rawReduceStepWordFromBits_refines
    (modulusWord : List Bool) (degree : Nat) (currentWord : List Bool)
    (hactive : 2 ^ degree ≤ rawBitsToNat currentWord) :
    rawBitsToNat
        (rawReduceStepWordFromBits modulusWord degree currentWord) =
      rawReduceStep (rawBitsToNat modulusWord) degree
        (rawBitsToNat currentWord) := by
  have hcurrent : rawBitsToNat currentWord ≠ 0 := by
    have hpow : 0 < 2 ^ degree := by positivity
    omega
  have hleading := rawBinaryWordLeadingOne_spec currentWord hcurrent
  have hindex : (rawBinaryWordLeadingOne currentWord).getD 0 =
      Nat.log2 (rawBitsToNat currentWord) := by
    rw [hleading]
    rfl
  unfold rawReduceStepWordFromBits
  rw [rawBinaryWordXor_refines_natXor,
    rawBinaryWordShiftLeft_refines, hindex]
  rw [Nat.mul_comm]
  rfl

/-- Fuel-bounded cancellation using only word-state threshold and leading-bit
scans. The stopping test is the Boolean threshold scan; the active branch
uses the word-level shifted modulus and XOR from `rawReduceStepWordFromBits`.
The state remains an arbitrary little-endian list, including trailing zero
padding. -/
def rawReduceFuelWordFromBits (modulusWord : List Bool) (degree : Nat) :
    Nat → List Bool → List Bool
  | 0, word => word
  | fuel + 1, word =>
      if rawBinaryWordBelowPowTwo degree word then word
      else rawReduceFuelWordFromBits modulusWord degree fuel
        (rawReduceStepWordFromBits modulusWord degree word)

/-- The word-state reducer refines the existing Nat-mask fuel recurrence for
every word input, modulus encoding, and fuel. In particular, both the stop
branch and the active cancellation branch agree with the existing program. -/
theorem rawReduceFuelWordFromBits_refines
    (modulusWord currentWord : List Bool) (degree fuel : Nat) :
    rawBitsToNat
        (rawReduceFuelWordFromBits modulusWord degree fuel currentWord) =
      rawReduceFuel (rawBitsToNat modulusWord) degree fuel
        (rawBitsToNat currentWord) := by
  induction fuel generalizing currentWord with
  | zero => rfl
  | succ fuel ih =>
      by_cases hsmall : rawBinaryWordBelowPowTwo degree currentWord = true
      · have hsmallNat : rawBitsToNat currentWord < 2 ^ degree := by
          have hspec := rawBinaryWordBelowPowTwo_spec degree currentWord
          rw [hsmall] at hspec
          exact of_decide_eq_true hspec.symm
        simp [rawReduceFuelWordFromBits, hsmall, rawReduceFuel, hsmallNat]
      · have hfalse : rawBinaryWordBelowPowTwo degree currentWord = false := by
          simpa using hsmall
        have hlargeNat : ¬ rawBitsToNat currentWord < 2 ^ degree := by
          have hspec := rawBinaryWordBelowPowTwo_spec degree currentWord
          rw [hfalse] at hspec
          exact of_decide_eq_false hspec.symm
        have hactive : 2 ^ degree ≤ rawBitsToNat currentWord :=
          Nat.le_of_not_gt hlargeNat
        have hstep := rawReduceStepWordFromBits_refines
          modulusWord degree currentWord hactive
        have hunfold : rawReduceFuelWordFromBits modulusWord degree
            (fuel + 1) currentWord =
              rawReduceFuelWordFromBits modulusWord degree fuel
                (rawReduceStepWordFromBits modulusWord degree currentWord) := by
          simp [rawReduceFuelWordFromBits, hfalse]
        have hrhs : rawReduceFuel (rawBitsToNat modulusWord) degree
            (fuel + 1) (rawBitsToNat currentWord) =
              rawReduceFuel (rawBitsToNat modulusWord) degree fuel
                (rawReduceStep (rawBitsToNat modulusWord) degree
                  (rawBitsToNat currentWord)) := by
          simp [rawReduceFuel, hlargeNat]
        rw [hunfold, hrhs, ← hstep]
        exact ih (rawReduceStepWordFromBits modulusWord degree currentWord)

end CorruptedFieldRecovery
