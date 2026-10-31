import CorruptedFieldRecovery.RawFieldArrayPolynomial
import CorruptedFieldRecovery.RawExecutableQuotient
import CorruptedFieldRecovery.RawPolynomialIrreducibility
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Bitwise

/-! A concrete little-endian bit-list implementation of word XOR and its
semantic connection to `Nat.xor`. The recursive program charges one Boolean
XOR gate for each output bit. The gate count does not include list traversal,
addressing, allocation, conversion between Nat and words, or evaluator stack;
it refines the XOR primitive only. -/

namespace CorruptedFieldRecovery

/-- One Boolean XOR gate. -/
def rawBinaryWordXorBit (a b : Bool) : Bool := decide (a ≠ b)

private theorem rawBinaryWordXorBit_eq_bne (a b : Bool) :
    rawBinaryWordXorBit a b = (a != b) := by
  cases a <;> cases b <;> rfl

/-- Little-endian word XOR, padding the shorter input with zero bits. -/
def rawBinaryWordXor : List Bool → List Bool → List Bool
  | [], [] => []
  | a :: as, [] => rawBinaryWordXorBit a false :: rawBinaryWordXor as []
  | [], b :: bs => rawBinaryWordXorBit false b :: rawBinaryWordXor [] bs
  | a :: as, b :: bs =>
      rawBinaryWordXorBit a b :: rawBinaryWordXor as bs
termination_by left right => left.length + right.length
decreasing_by all_goals simp_wf <;> omega

/-- The list routine produces one output cell, and hence one Boolean XOR
gate, per bit position up to the longer input width. -/
theorem rawBinaryWordXor_length (left right : List Bool) :
    (rawBinaryWordXor left right).length = max left.length right.length := by
  induction left generalizing right with
  | nil =>
      induction right with
      | nil => simp [rawBinaryWordXor]
      | cons b bs ih => simp [rawBinaryWordXor, ih]
  | cons a as ih =>
      cases right with
      | nil => simp [rawBinaryWordXor, ih]
      | cons b bs => simp [rawBinaryWordXor, ih]

/-- The represented bit-list computation decodes to the core `Nat.xor`
operation, for inputs of unequal as well as equal width. -/
theorem rawBinaryWordXor_refines_natXor (left right : List Bool) :
    rawBitsToNat (rawBinaryWordXor left right) =
      Nat.xor (rawBitsToNat left) (rawBitsToNat right) := by
  induction left generalizing right with
  | nil =>
      induction right with
      | nil => simp [rawBinaryWordXor, rawBitsToNat]
      | cons b bs tail_ih =>
          simp [rawBinaryWordXor, rawBitsToNat_cons,
            rawBitsToNat, rawBinaryWordXorBit_eq_bne, tail_ih]
          simpa [rawBitsToNat] using (rawBitsToNat_cons b bs).symm
  | cons a as ih =>
      cases right with
      | nil =>
          simp [rawBinaryWordXor, rawBitsToNat_cons,
            rawBitsToNat, rawBinaryWordXorBit_eq_bne, ih]
          simpa [rawBitsToNat] using (rawBitsToNat_cons a as).symm
      | cons b bs =>
          simp [rawBinaryWordXor, rawBitsToNat_cons,
            rawBinaryWordXorBit_eq_bne, Nat.xor_bit, ih]

/-- The repository's little-endian decoder maps Mathlib's canonical Nat bit
list back to the represented natural number. -/
theorem rawBitsToNat_natBits (value : Nat) :
    rawBitsToNat value.bits = value := by
  induction value using Nat.binaryRec' with
  | zero => simp [rawBitsToNat]
  | bit b n h ih =>
      rw [Nat.bits_append_bit n b h]
      simp [rawBitsToNat_cons, Nat.bit, ih]

/-- On canonical Nat bit representations, the concrete list algorithm
decodes to the core natural-number XOR. -/
theorem rawNatBitsXor_refines_natXor (left right : Nat) :
    rawBitsToNat (rawBinaryWordXor left.bits right.bits) =
      Nat.xor left right := by
  rw [rawBinaryWordXor_refines_natXor,
    rawBitsToNat_natBits, rawBitsToNat_natBits]

/-- A low-endian word shift: inserting `shift` zero bits at the low end. -/
def rawBinaryWordShiftLeft (shift : Nat) (word : List Bool) : List Bool :=
  List.replicate shift false ++ word

theorem rawBitsToNat_replicate_false (shift : Nat) :
    rawBitsToNat (List.replicate shift false) = 0 := by
  induction shift with
  | zero => rfl
  | succ shift ih =>
      rw [List.replicate_succ, rawBitsToNat_cons]
      simp [ih]

/-- The word shift denotes multiplication by the corresponding power of two. -/
theorem rawBinaryWordShiftLeft_refines (shift : Nat) (word : List Bool) :
    rawBitsToNat (rawBinaryWordShiftLeft shift word) =
      2 ^ shift * rawBitsToNat word := by
  rw [rawBinaryWordShiftLeft, rawBitsToNat_append,
    rawBitsToNat_replicate_false]
  simp

theorem rawBinaryWordShiftLeft_length (shift : Nat) (word : List Bool) :
    (rawBinaryWordShiftLeft shift word).length = shift + word.length := by
  simp [rawBinaryWordShiftLeft]

/-- A word-based implementation of the reducer's cancellation result. Only
the cancellation XOR and multiplication by a power of two are implemented on
Boolean words here. Logarithm, shift-count computation, and the Nat-to-word
boundary remain explicit unrefined operations. -/
def rawReduceStepWord (modulus degree current : Nat) : List Bool :=
  rawBinaryWordXor current.bits
    (rawBinaryWordShiftLeft (Nat.log2 current - degree) modulus.bits)

theorem rawReduceStepWord_refines (modulus degree current : Nat) :
    rawBitsToNat (rawReduceStepWord modulus degree current) =
      rawReduceStep modulus degree current := by
  rw [rawReduceStepWord, rawBinaryWordXor_refines_natXor,
    rawBitsToNat_natBits, rawBinaryWordShiftLeft_refines,
    rawBitsToNat_natBits]
  rw [Nat.mul_comm]
  rfl

/-- Gate count for this Boolean-word implementation: one Boolean XOR gate
per output bit, excluding traversal, addressing, and storage operations. -/
def rawBinaryWordXorGateCount (left right : List Bool) : Nat :=
  (rawBinaryWordXor left right).length

theorem rawBinaryWordXorGateCount_eq_width (left right : List Bool) :
    rawBinaryWordXorGateCount left right = max left.length right.length :=
  rawBinaryWordXor_length left right

/-- Exact Boolean XOR-gate count for a reducer cancellation when the operands
are supplied as canonical bit words. This is not a total reducer charge. -/
theorem rawReduceStepWord_gateCount (modulus degree current : Nat) :
    rawBinaryWordXorGateCount current.bits
      (rawBinaryWordShiftLeft (Nat.log2 current - degree) modulus.bits) =
    max current.bits.length
      ((Nat.log2 current - degree) + modulus.bits.length) := by
  rw [rawBinaryWordXorGateCount_eq_width,
    rawBinaryWordShiftLeft_length]

end CorruptedFieldRecovery
