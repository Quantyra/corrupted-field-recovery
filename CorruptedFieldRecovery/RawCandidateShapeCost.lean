import CorruptedFieldRecovery.RawRabinCandidateCorrectness
import CorruptedFieldRecovery.RawPolynomialBitCost

/-! A width-charged recurrence for the actual raw-bit decoder and the
short-circuit structural checks used before the Rabin scan. Charges here are
an explicit bit-operation model, not a claim about Lean runtime. -/

namespace CorruptedFieldRecovery

/-- Decode a little-endian bit list with a declared shift/add bit charge at
each recursive return. -/
def rawBitsToNatBitCosted : List Bool → Nat × Nat
  | [] => (0, 0)
  | bit :: tail =>
      let decoded := rawBitsToNatBitCosted tail
      ((if bit then 1 else 0) + 2 * decoded.1,
        decoded.2 + rawNatBitWidth decoded.1 + 1)

theorem rawBitsToNatBitCosted_fst (bits : List Bool) :
    (rawBitsToNatBitCosted bits).1 = rawBitsToNat bits := by
  induction bits with
  | nil => rfl
  | cons bit tail ih =>
      simp [rawBitsToNatBitCosted, rawBitsToNat, ih]

/-- Include the list conversion performed by `rawFieldBitsToNat` in the
decoder charge, one cell visit per array bit. -/
def rawFieldBitsToNatBitCosted (bits : RawFieldBits) : Nat × Nat :=
  let decoded := rawBitsToNatBitCosted bits.toList
  (decoded.1, decoded.2 + bits.size)

theorem rawFieldBitsToNatBitCosted_fst (bits : RawFieldBits) :
    (rawFieldBitsToNatBitCosted bits).1 = rawFieldBitsToNat bits := by
  simp [rawFieldBitsToNatBitCosted, rawFieldBitsToNat,
    rawBitsToNatBitCosted_fst]

/-- Declared cost of comparing two unsigned binary words bit by bit. -/
def rawShapeCompareCharge (a b : Nat) : Nat :=
  rawNatBitWidth a + rawNatBitWidth b

/-- Declared long-division charge: a bitwise quotient/remainder pass over
the dividend and divisor widths. -/
def rawShapeDivisionCharge (a b : Nat) : Nat :=
  2 * (rawNatBitWidth a + rawNatBitWidth b + 1) ^ 2

/-- The actual structural gate, instrumented in the same short-circuit order:
dimension, modulus length, modulus top coefficient, scalar length, scalar
nonzero. Array-to-list and shift/add decoding are included when reached. -/
def rawFieldCandidateShapeCheckBitCosted {s : Nat}
    (candidate : RawFieldCandidate s) : Bool × Nat :=
  let dimensionTest := decide (1 ≤ s)
  let dimensionCharge := rawShapeCompareCharge 1 s
  if dimensionTest then
    let modulusSizeTest := decide (candidate.modulus.size = s + 1)
    let modulusSizeCharge := rawShapeCompareCharge candidate.modulus.size (s + 1)
    if modulusSizeTest then
      let modulus := rawFieldBitsToNatBitCosted candidate.modulus
      let power := 2 ^ s
      let quotient := modulus.1 / power
      let residue := quotient % 2
      let topTest := decide (residue = 1)
      let topCharge := modulus.2 + s +
        rawShapeDivisionCharge modulus.1 power +
        rawShapeDivisionCharge quotient 2 + rawShapeCompareCharge residue 1
      if topTest then
        let scalarSizeTest := decide (candidate.scalar.size = s)
        let scalarSizeCharge := rawShapeCompareCharge candidate.scalar.size s
        if scalarSizeTest then
          let scalar := rawFieldBitsToNatBitCosted candidate.scalar
          (decide (scalar.1 ≠ 0), dimensionCharge + modulusSizeCharge +
            topCharge + scalarSizeCharge + scalar.2 + rawNatBitWidth scalar.1)
        else
          (false, dimensionCharge + modulusSizeCharge + topCharge + scalarSizeCharge)
      else
        (false, dimensionCharge + modulusSizeCharge + topCharge)
    else
      (false, dimensionCharge + modulusSizeCharge)
  else
    (false, dimensionCharge)

theorem rawFieldCandidateShapeCheckBitCosted_fst {s : Nat}
    (candidate : RawFieldCandidate s) :
    (rawFieldCandidateShapeCheckBitCosted candidate).1 =
      rawFieldCandidateShapeCheck candidate := by
  cases hdim : decide (1 ≤ s) <;>
    cases hmod : decide (candidate.modulus.size = s + 1) <;>
    cases htop : decide
      (rawFieldBitsToNat candidate.modulus / 2 ^ s % 2 = 1) <;>
    cases hsize : decide (candidate.scalar.size = s) <;>
    cases hscalar : decide (rawFieldBitsToNat candidate.scalar ≠ 0) <;>
    simp [rawFieldCandidateShapeCheckBitCosted, rawFieldCandidateShapeCheck,
      rawFieldBitsToNatBitCosted_fst, hdim, hmod, htop, hsize, hscalar]

end CorruptedFieldRecovery
