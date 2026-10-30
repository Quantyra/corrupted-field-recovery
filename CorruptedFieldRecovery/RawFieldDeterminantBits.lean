import CorruptedFieldRecovery.RawFieldTraceBitValue
import CorruptedFieldRecovery.FourContractions

/-! Actual Nat-mask determinant and trace computation over the checked raw
quotient field. The arguments here are the three little-endian coordinate
masks for each physical vector; a separate coordinate decoder supplies them. -/

namespace CorruptedFieldRecovery

/-- Three successive raw quotient multiplications. -/
def rawFieldMul3Bits {s : Nat} (candidate : RawFieldCandidate s)
    (hcheck : rawFieldCandidateCheck candidate = true) (a b c : Nat) : Nat :=
  rawFieldMulBits candidate hcheck (rawFieldMulBits candidate hcheck a b) c

/-- The six-term determinant expansion in characteristic two, computed with
the executable carryless multiplication/reduction and XOR routines. -/
def rawFieldDet3Bits {s : Nat} (candidate : RawFieldCandidate s)
    (hcheck : rawFieldCandidateCheck candidate = true)
    (x y z : Nat × Nat × Nat) : Nat :=
  Nat.xor
    (rawFieldMul3Bits candidate hcheck x.1 y.2.1 z.2.2)
    (Nat.xor
      (rawFieldMul3Bits candidate hcheck x.1 y.2.2 z.2.1)
      (Nat.xor
        (rawFieldMul3Bits candidate hcheck y.1 x.2.1 z.2.2)
        (Nat.xor
          (rawFieldMul3Bits candidate hcheck y.1 x.2.2 z.2.1)
          (Nat.xor
            (rawFieldMul3Bits candidate hcheck z.1 x.2.1 y.2.2)
            (rawFieldMul3Bits candidate hcheck z.1 x.2.2 y.2.1)))))

/-- Compute the determinant mask, multiply by the candidate scalar, and run
the bit-level trace evaluator. -/
def rawFieldTraceDet3Bits {s : Nat} (candidate : RawFieldCandidate s)
    (hcheck : rawFieldCandidateCheck candidate = true)
    (x y z : Nat × Nat × Nat) : Nat :=
  rawFieldTraceBits candidate hcheck
    (rawFieldMulBits candidate hcheck (rawFieldBitsToNat candidate.scalar)
      (rawFieldDet3Bits candidate hcheck x y z))

/-- The executable six-term determinant mask denotes the field determinant
of the three decoded coordinate triples. -/
theorem rawFieldDet3Bits_quotient_sound {s : Nat}
    (candidate : RawFieldCandidate s)
    (hcheck : rawFieldCandidateCheck candidate = true)
    (x y z : Nat × Nat × Nat) :
    rawCandidateQuotientClass candidate (rawFieldDet3Bits candidate hcheck x y z) =
      fieldDet3
        (rawCandidateQuotientClass candidate x.1,
          rawCandidateQuotientClass candidate x.2.1,
          rawCandidateQuotientClass candidate x.2.2)
        (rawCandidateQuotientClass candidate y.1,
          rawCandidateQuotientClass candidate y.2.1,
          rawCandidateQuotientClass candidate y.2.2)
        (rawCandidateQuotientClass candidate z.1,
          rawCandidateQuotientClass candidate z.2.1,
          rawCandidateQuotientClass candidate z.2.2) := by
  letI : Fact (Irreducible (rawCandidateModulus candidate)) :=
    ⟨accepted_rawCandidateModulus_irreducible candidate hcheck⟩
  let K := AdjoinRoot (rawCandidateModulus candidate)
  have htwo : (2 : K) = 0 := by
    calc
      (2 : K) = 1 + 1 := by norm_num
      _ = algebraMap (ZMod 2) K (1 : ZMod 2) +
            algebraMap (ZMod 2) K (1 : ZMod 2) := by simp
      _ = algebraMap (ZMod 2) K ((1 : ZMod 2) + 1) := by rw [← map_add]
      _ = algebraMap (ZMod 2) K 0 := by
        rw [show (1 : ZMod 2) + 1 = 0 by decide]
      _ = 0 := map_zero _
  letI : CharP K 2 :=
    CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero htwo
  simp only [rawFieldDet3Bits, rawFieldMul3Bits]
  repeat' rw [rawFieldAddBits_quotient_sound]
  repeat' rw [rawFieldMulBits_quotient_sound]
  simp only [fieldDet3, CharTwo.sub_eq_add]
  ring_nf

/-- The final raw result is exactly the base-field trace bit of scalar times
the algebraic determinant. This theorem connects every bit-level arithmetic
operation used by the determinant evaluator to the field semantics. -/
theorem rawFieldTraceDet3Bits_eq_baseTrace {s : Nat}
    (candidate : RawFieldCandidate s)
    (hcheck : rawFieldCandidateCheck candidate = true)
    (x y z : Nat × Nat × Nat) :
    rawFieldTraceDet3Bits candidate hcheck x y z =
      if Algebra.trace (ZMod 2) (AdjoinRoot (rawCandidateModulus candidate))
          (rawCandidateQuotientClass candidate (rawFieldBitsToNat candidate.scalar) *
            fieldDet3
              (rawCandidateQuotientClass candidate x.1,
                rawCandidateQuotientClass candidate x.2.1,
                rawCandidateQuotientClass candidate x.2.2)
              (rawCandidateQuotientClass candidate y.1,
                rawCandidateQuotientClass candidate y.2.1,
                rawCandidateQuotientClass candidate y.2.2)
              (rawCandidateQuotientClass candidate z.1,
                rawCandidateQuotientClass candidate z.2.1,
                rawCandidateQuotientClass candidate z.2.2)) = 0 then 0 else 1 := by
  letI : Fact (Irreducible (rawCandidateModulus candidate)) :=
    ⟨accepted_rawCandidateModulus_irreducible candidate hcheck⟩
  let K := AdjoinRoot (rawCandidateModulus candidate)
  have htraceInput :
      rawFieldMulBits candidate hcheck (rawFieldBitsToNat candidate.scalar)
        (rawFieldDet3Bits candidate hcheck x y z) < 2 ^ s := by
    simpa [rawFieldMulBits] using
      rawFieldMulFuel_lt_of_accepted candidate hcheck
        (rawFieldBitsToNat candidate.scalar) (rawFieldDet3Bits candidate hcheck x y z)
  have hscaled := rawFieldMulBits_quotient_sound candidate hcheck
    (rawFieldBitsToNat candidate.scalar) (rawFieldDet3Bits candidate hcheck x y z)
  have hsemantic :
      rawCandidateQuotientClass candidate
          (rawFieldMulBits candidate hcheck (rawFieldBitsToNat candidate.scalar)
            (rawFieldDet3Bits candidate hcheck x y z)) =
        rawCandidateQuotientClass candidate (rawFieldBitsToNat candidate.scalar) *
          fieldDet3
            (rawCandidateQuotientClass candidate x.1,
              rawCandidateQuotientClass candidate x.2.1,
              rawCandidateQuotientClass candidate x.2.2)
            (rawCandidateQuotientClass candidate y.1,
              rawCandidateQuotientClass candidate y.2.1,
              rawCandidateQuotientClass candidate y.2.2)
            (rawCandidateQuotientClass candidate z.1,
              rawCandidateQuotientClass candidate z.2.1,
              rawCandidateQuotientClass candidate z.2.2) := by
    rw [hscaled, rawFieldDet3Bits_quotient_sound candidate hcheck x y z]
  have htrace := congrArg (Algebra.trace (ZMod 2) K) hsemantic
  rw [rawFieldTraceDet3Bits, rawFieldTraceBits_eq_baseBit candidate hcheck _ htraceInput]
  simpa [K] using congrArg (fun q : ZMod 2 => if q = 0 then 0 else 1) htrace

end CorruptedFieldRecovery
