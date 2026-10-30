import CorruptedFieldRecovery.RawPhysicalCoordinateCorrespondence
import CorruptedFieldRecovery.RawPhysicalTraceBits

/-! Compose checked inverse-matrix decoding, exact physical block masks, and
the executable determinant/trace evaluator. -/

namespace CorruptedFieldRecovery

open AdjoinRoot

/-- Decode one physical vector through the checked inverse matrix and then
the canonical power-basis coordinate equivalence. -/
noncomputable def rawPhysicalCanonicalTriple {s : Nat}
    (candidate : RawFieldCandidate s)
    (hcheck : rawFieldCandidateCheck candidate = true)
    (inverse : RawCoordinateMatrix) (v : BinaryVector (3 * s)) :
    FieldTriple (AdjoinRoot (rawCandidateModulus candidate)) :=
  (rawFieldTripleToBinaryVector (rawCandidateModulus candidate)
    (accepted_rawCandidateModulus_monic candidate hcheck)
    (by
      have hv := accepted_rawFieldCandidateCheck candidate hcheck
      have hm := rawFieldCandidateValid_modulus_polynomial candidate hv
      simpa [rawCandidateModulus] using hm.2)).symm
    (rawCoordinateMatrixMap inverse v)

/-- The three executable masks decode to the same field triple as the
accepted inverse-matrix and power-basis coordinate maps. -/
theorem rawPhysicalTripleMasks_eq_canonical {s : Nat}
    (candidate : RawFieldCandidate s)
    (hcheck : rawFieldCandidateCheck candidate = true)
    (inverse : RawCoordinateMatrix) (v : BinaryVector (3 * s)) :
    (rawCandidateQuotientClass candidate (rawPhysicalTripleMasks inverse v).1,
      (rawCandidateQuotientClass candidate (rawPhysicalTripleMasks inverse v).2.1,
       rawCandidateQuotientClass candidate (rawPhysicalTripleMasks inverse v).2.2)) =
      rawPhysicalCanonicalTriple candidate hcheck inverse v := by
  apply Prod.ext
  · change rawCandidateQuotientClass candidate
      (rawPhysicalBlockMask (rawCoordinateMatrixMap inverse v) 0) = _
    simpa [rawFieldTripleComponent] using
      rawPhysicalBlockMask_eq_canonicalComponent candidate hcheck
        (rawCoordinateMatrixMap inverse v) 0
  · apply Prod.ext
    · change rawCandidateQuotientClass candidate
        (rawPhysicalBlockMask (rawCoordinateMatrixMap inverse v) 1) = _
      simpa [rawFieldTripleComponent] using
        rawPhysicalBlockMask_eq_canonicalComponent candidate hcheck
          (rawCoordinateMatrixMap inverse v) 1
    · change rawCandidateQuotientClass candidate
        (rawPhysicalBlockMask (rawCoordinateMatrixMap inverse v) 2) = _
      simpa [rawFieldTripleComponent] using
        rawPhysicalBlockMask_eq_canonicalComponent candidate hcheck
          (rawCoordinateMatrixMap inverse v) 2

/-- The executable physical coefficient is the base trace bit of the
determinant of the three canonically decoded field triples. -/
theorem rawPhysicalTraceDet3Bits_eq_canonicalTrace {s : Nat}
    (candidate : RawFieldCandidate s)
    (hfield : rawFieldCandidateCheck candidate = true)
    (inverse : RawCoordinateMatrix)
    (x y z : BinaryVector (3 * s)) :
    rawPhysicalTraceDet3Bits candidate hfield inverse x y z =
      if Algebra.trace (ZMod 2) (AdjoinRoot (rawCandidateModulus candidate))
          (rawCandidateQuotientClass candidate (rawFieldBitsToNat candidate.scalar) *
            fieldDet3 (rawPhysicalCanonicalTriple candidate hfield inverse x)
              (rawPhysicalCanonicalTriple candidate hfield inverse y)
              (rawPhysicalCanonicalTriple candidate hfield inverse z)) = 0
        then 0 else 1 := by
  rw [rawPhysicalTraceDet3Bits_eq_baseTrace]
  rw [← rawPhysicalTripleMasks_eq_canonical candidate hfield inverse x]
  rw [← rawPhysicalTripleMasks_eq_canonical candidate hfield inverse y]
  rw [← rawPhysicalTripleMasks_eq_canonical candidate hfield inverse z]

end CorruptedFieldRecovery
