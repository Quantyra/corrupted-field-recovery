import CorruptedFieldRecovery.RawFieldDeterminantBits
import CorruptedFieldRecovery.RawCoordinateEquivalence

/-! Execute the accepted inverse binary coordinate transform on physical
vectors, split the result into the three little-endian power-basis blocks,
and pass those masks to the raw determinant/trace evaluator. -/

namespace CorruptedFieldRecovery

/-- Read one little-endian `s`-bit block from a serialized `3s`-coordinate
vector and turn it into a Nat mask. -/
def rawPhysicalBlockMask {s : Nat} (v : BinaryVector (3 * s)) (block : Fin 3) : Nat :=
  rawBitsToNat (List.ofFn fun i : Fin s =>
    decide (v (finProdFinEquiv (block, i)) = (1 : ZMod 2)))

/-- Apply the supplied serialized inverse matrix and split into the three
field-coordinate masks used by the executable determinant evaluator. -/
def rawPhysicalTripleMasks {s : Nat} (inverse : RawCoordinateMatrix)
    (v : BinaryVector (3 * s)) : Nat × Nat × Nat :=
  let w := rawCoordinateMatrixMap inverse v
  (rawPhysicalBlockMask w 0, rawPhysicalBlockMask w 1, rawPhysicalBlockMask w 2)

/-- Per-triple executable trace coefficient from three physical coordinate
vectors. -/
def rawPhysicalTraceDet3Bits {s : Nat} (candidate : RawFieldCandidate s)
    (hfield : rawFieldCandidateCheck candidate = true)
    (inverse : RawCoordinateMatrix)
    (x y z : BinaryVector (3 * s)) : Nat :=
  rawFieldTraceDet3Bits candidate hfield
    (rawPhysicalTripleMasks inverse x)
    (rawPhysicalTripleMasks inverse y)
    (rawPhysicalTripleMasks inverse z)

/-- The checked pair of serialized matrices makes `inverse` undo `forward`
on every physical-coordinate vector. -/
theorem accepted_rawPhysicalCoordinateInverse {s : Nat}
    (forward inverse : RawCoordinateMatrix)
    (hcoordinates : rawCoordinateMatrixCheck (n := 3 * s) forward inverse = true)
    (v : BinaryVector (3 * s)) :
    rawCoordinateMatrixMap inverse (rawCoordinateMatrixMap forward v) = v := by
  have hcomp := accepted_rawCoordinateMatrixCheck_compositions forward inverse hcoordinates
  have h := congrArg
    (fun f : BinaryVector (3 * s) →ₗ[ZMod 2] BinaryVector (3 * s) => f v) hcomp.1
  simpa [LinearMap.comp_apply] using h

/-- The physical-vector evaluator is the determinant/trace mask computation
on precisely the inverse-matrix coordinate blocks extracted from each input. -/
theorem rawPhysicalTraceDet3Bits_eq_baseTrace {s : Nat}
    (candidate : RawFieldCandidate s)
    (hfield : rawFieldCandidateCheck candidate = true)
    (inverse : RawCoordinateMatrix)
    (x y z : BinaryVector (3 * s)) :
    rawPhysicalTraceDet3Bits candidate hfield inverse x y z =
      if Algebra.trace (ZMod 2) (AdjoinRoot (rawCandidateModulus candidate))
          (rawCandidateQuotientClass candidate (rawFieldBitsToNat candidate.scalar) *
            fieldDet3
              (rawCandidateQuotientClass candidate (rawPhysicalTripleMasks inverse x).1,
                rawCandidateQuotientClass candidate (rawPhysicalTripleMasks inverse x).2.1,
                rawCandidateQuotientClass candidate (rawPhysicalTripleMasks inverse x).2.2)
              (rawCandidateQuotientClass candidate (rawPhysicalTripleMasks inverse y).1,
                rawCandidateQuotientClass candidate (rawPhysicalTripleMasks inverse y).2.1,
                rawCandidateQuotientClass candidate (rawPhysicalTripleMasks inverse y).2.2)
              (rawCandidateQuotientClass candidate (rawPhysicalTripleMasks inverse z).1,
                rawCandidateQuotientClass candidate (rawPhysicalTripleMasks inverse z).2.1,
                rawCandidateQuotientClass candidate (rawPhysicalTripleMasks inverse z).2.2)) = 0 then 0 else 1 := by
  simpa [rawPhysicalTraceDet3Bits] using
    rawFieldTraceDet3Bits_eq_baseTrace candidate hfield
      (rawPhysicalTripleMasks inverse x)
      (rawPhysicalTripleMasks inverse y)
      (rawPhysicalTripleMasks inverse z)

end CorruptedFieldRecovery
