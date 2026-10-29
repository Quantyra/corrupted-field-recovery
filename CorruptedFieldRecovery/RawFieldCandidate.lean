import Mathlib.Data.ZMod.Basic

/-! Finite raw-bit polynomial arithmetic for the field-candidate gate.

Bits are little-endian: bit `i` is the coefficient of `X^i`. These routines
avoid the noncomputable generic `Polynomial` ring instance. The candidate
gate enumerates every possible monic factor through half the degree and
checks every bounded factor/quotient product. The bridge from these bit
operations to the library's polynomial `Irreducible` predicate remains a
separate theorem.
-/

namespace CorruptedFieldRecovery

abbrev RawFieldBits := Array Bool

structure RawFieldCandidate (s : Nat) where
  modulus : RawFieldBits
  scalar : RawFieldBits

/-- Interpret a low-endian bit list as its natural-number bit mask. -/
def rawBitsToNat : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * rawBitsToNat bs

def rawFieldBitsToNat (bits : RawFieldBits) : Nat := rawBitsToNat bits.toList

/-- Carryless multiplication of bit masks, with addition represented by XOR. -/
def rawPolyMul (a b : Nat) : Nat :=
  if b = 0 then 0
  else Nat.xor (if b % 2 = 1 then a else 0) (2 * rawPolyMul a (b / 2))
termination_by b
decreasing_by
  have hb : 0 < b := Nat.pos_of_ne_zero (by assumption)
  exact Nat.div_lt_self hb (by decide)

/-- No monic proper factorization of the encoded polynomial. Candidate masks
in `[2^d, 2^(d+1))` have degree exactly `d`; quotient masks are bounded by the
remaining degree. This checks products directly and uses no division fuel. -/
def rawIrreducible (p s : Nat) : Prop :=
  ∀ d ∈ Finset.Icc 1 (s / 2),
    ∀ g ∈ Finset.Ico (2 ^ d) (2 ^ (d + 1)),
      ∀ q ∈ Finset.range (2 ^ (s - d + 1)), rawPolyMul g q ≠ p

/-- Exact candidate recognition conditions on the raw arrays. -/
def rawFieldCandidateValid {s : Nat} (p : RawFieldCandidate s) : Prop :=
  1 ≤ s ∧
  p.modulus.size = s + 1 ∧
  rawFieldBitsToNat p.modulus / 2 ^ s % 2 = 1 ∧
  p.scalar.size = s ∧
  rawFieldBitsToNat p.scalar ≠ 0 ∧
  rawIrreducible (rawFieldBitsToNat p.modulus) s

/-- Explicit constructive decidability for the finite raw predicate. -/
def rawFieldCandidateValidDecidable {s : Nat} (p : RawFieldCandidate s) :
    Decidable (rawFieldCandidateValid p) := by
  unfold rawFieldCandidateValid rawIrreducible
  infer_instance

/-- Deterministic finite divisor-enumeration gate. All branches range over
finite arrays, natural-number arithmetic, and finite sets. -/
def rawFieldCandidateCheck {s : Nat} (p : RawFieldCandidate s) : Bool :=
  @decide (rawFieldCandidateValid p) (rawFieldCandidateValidDecidable p)

theorem accepted_rawFieldCandidateCheck {s : Nat} (p : RawFieldCandidate s)
    (h : rawFieldCandidateCheck p = true) : rawFieldCandidateValid p :=
  @of_decide_eq_true _ (rawFieldCandidateValidDecidable p)
    (by simpa [rawFieldCandidateCheck] using h)

/-- The degree-one moduli `X` and `X+1` have no possible divisor degree in
the tested interval, so both serialized cases remain accepted. -/
theorem rawFieldCandidateCheck_degreeOneX : rawFieldCandidateCheck
    (⟨#[false, true], #[true]⟩ : RawFieldCandidate 1) = true := by decide

theorem rawFieldCandidateCheck_degreeOneXAddOne : rawFieldCandidateCheck
    (⟨#[true, true], #[true]⟩ : RawFieldCandidate 1) = true := by decide

end CorruptedFieldRecovery
