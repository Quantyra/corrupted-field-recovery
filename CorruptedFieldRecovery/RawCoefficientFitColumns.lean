import CorruptedFieldRecovery.RawPhysicalTraceBits
import CorruptedFieldRecovery.RawVerifier

/-! # Computable columns for the raw coefficient-fit system

This file constructs entries of the rectangular fit matrix used by the
coefficient reconstruction step. Rows are the serialized increasing physical
triples in `IncreasingTriple (3*s)`. Columns are tagged either by a scalar
power-basis position `j : Fin s`, or by an increasing support triple in
`IncreasingTriple d`. The latter are the six-term exterior-support columns.

The definitions below are executable finite computations. In particular,
they do not call `rawTraceDetPayload`, choose a quotient-field basis, search
for fitting coefficients, or assert that the fit has a solution. The semantic
equalities to the manuscript's abstract columns, the flattening into the
solver's row/column array order, and existence of a solution remain separate
proof obligations.
-/

namespace CorruptedFieldRecovery

/-- Little-endian raw bits for the power-basis vector `X^j`. Bit `j` is the
only set bit. -/
def rawUnitScalarBits (s : Nat) (j : Fin s) : RawFieldBits :=
  (List.ofFn fun i : Fin s => decide (i = j)).toArray

/-- The existing trace/determinant evaluator with its scalar supplied
separately. This is definitionally the same finite multiplication,
determinant, and trace computation as `rawFieldTraceDet3Bits`, but permits
constructing one fit column for each scalar coefficient without changing the
candidate's already-checked modulus. -/
def rawFieldTraceDet3WithScalarBits {s : Nat}
    (candidate : RawFieldCandidate s)
    (hcheck : rawFieldCandidateCheck candidate = true)
    (scalarBits : RawFieldBits) (x y z : Nat × Nat × Nat) : Nat :=
  rawFieldTraceBits candidate hcheck
    (rawFieldMulBits candidate hcheck (rawFieldBitsToNat scalarBits)
      (rawFieldDet3Bits candidate hcheck x y z))

/-- Convert the raw Nat trace result to the corresponding base-field bit.
For accepted candidates the evaluator's semantic theorem shows the result is
always `0` or `1`; this total conversion also defines behavior on malformed
inputs. -/
def rawNatTraceBit (a : Nat) : ZMod 2 :=
  if a = 0 then 0 else 1

/-- One trace-determinant coefficient column, indexed by a scalar power-basis
coordinate. Its entries are obtained from the existing raw evaluator on
physical coordinate unit vectors after the supplied inverse coordinate map.
The scalar input is exactly the one-hot little-endian bit array. -/
def rawTraceUnitFitColumn {s : Nat}
    (candidate : RawFieldCandidate s)
    (hcheck : rawFieldCandidateCheck candidate = true)
    (inverse : RawCoordinateMatrix) (j : Fin s) :
    IncreasingTriple (3 * s) → ZMod 2 := fun t =>
  rawNatTraceBit (rawFieldTraceDet3WithScalarBits candidate hcheck
    (rawUnitScalarBits s j)
    (rawPhysicalTripleMasks inverse
      (coordinateVectorCode (increasingTripleI t)))
    (rawPhysicalTripleMasks inverse
      (coordinateVectorCode (increasingTripleJ t)))
    (rawPhysicalTripleMasks inverse
      (coordinateVectorCode (increasingTripleK t))))

/-- One exterior-support column. For a support triple `(i,j,k)`, evaluate its
six-term alternating minor on the three support images of the physical
coordinate unit vectors. This is the raw, computable coefficient of the
pullback of the corresponding support minor. -/
def rawExteriorSupportFitColumn {s d : Nat}
    (supportMatrix : RawBinaryArray) (supportTriple : IncreasingTriple d) :
    IncreasingTriple (3 * s) → ZMod 2 := fun t =>
  minorTensor (increasingTripleI supportTriple)
      (increasingTripleJ supportTriple) (increasingTripleK supportTriple)
    (rawSupportMap (n := 3 * s) (d := d) supportMatrix
      (coordinateVectorCode (increasingTripleI t)))
    (rawSupportMap (n := 3 * s) (d := d) supportMatrix
      (coordinateVectorCode (increasingTripleJ t)))
    (rawSupportMap (n := 3 * s) (d := d) supportMatrix
      (coordinateVectorCode (increasingTripleK t)))

/-- Disjoint sum index for the complete fit matrix: the left summand contains
the `s` trace-scalar unknowns and the right summand contains the increasing
support triples. The semantic matrix therefore has `Fintype.card
(IncreasingTriple (3*s))` rows and `s + Fintype.card (IncreasingTriple d)`
columns. This source-indexed form avoids introducing a noncomputable basis or
an unproved flattening convention. -/
abbrev RawCoefficientFitColumnIndex (s d : Nat) :=
  Fin s ⊕ IncreasingTriple d

/-- Computable entry function for the rectangular raw fit matrix. The column
ordering is explicit in the `Sum` tag and does not depend on an implicit
choice of basis. -/
def rawCoefficientFitEntry {s d : Nat}
    (candidate : RawFieldCandidate s)
    (hcheck : rawFieldCandidateCheck candidate = true)
    (inverse : RawCoordinateMatrix) (supportMatrix : RawBinaryArray)
    (row : IncreasingTriple (3 * s))
    (column : RawCoefficientFitColumnIndex s d) : ZMod 2 :=
  match column with
  | Sum.inl j => rawTraceUnitFitColumn candidate hcheck inverse j row
  | Sum.inr e => rawExteriorSupportFitColumn supportMatrix e row

/-- The actual serialized right-hand-side coefficient at a row. The caller
must establish `raw.size = (3*s)^3` before using it as the manuscript input;
the array read itself remains total and returns the standard default value
when that shape condition is absent. -/
def rawCoefficientFitRhs {s : Nat} (raw : RawCoefficientArray)
    (row : IncreasingTriple (3 * s)) : ZMod 2 :=
  raw[rawCoefficientOffset (3 * s) (increasingTripleI row)
    (increasingTripleJ row) (increasingTripleK row)]!

/-- The entry equation for a trace-scalar column is by construction the
existing bit-level physical trace/determinant evaluator with scalar bits
`rawUnitScalarBits s j`. This equality is definitional; no claim is made here
that its semantic field value is the `X^j` column until the polynomial-mask
interpretation theorem is supplied. -/
theorem rawCoefficientFitEntry_traceColumn {s d : Nat}
    (candidate : RawFieldCandidate s)
    (hcheck : rawFieldCandidateCheck candidate = true)
    (inverse : RawCoordinateMatrix) (supportMatrix : RawBinaryArray)
    (row : IncreasingTriple (3 * s)) (j : Fin s) :
    rawCoefficientFitEntry candidate hcheck inverse supportMatrix row
        (Sum.inl j : RawCoefficientFitColumnIndex s d) =
      rawTraceUnitFitColumn candidate hcheck inverse j row := by
  rfl

/-- The entry equation for an exterior-support column is by construction the
six-term minor evaluated on the serialized support-map images of the three
physical coordinate vectors. -/
theorem rawCoefficientFitEntry_supportColumn {s d : Nat}
    (candidate : RawFieldCandidate s)
    (hcheck : rawFieldCandidateCheck candidate = true)
    (inverse : RawCoordinateMatrix) (supportMatrix : RawBinaryArray)
    (row : IncreasingTriple (3 * s)) (e : IncreasingTriple d) :
    rawCoefficientFitEntry candidate hcheck inverse supportMatrix row
        (Sum.inr e : RawCoefficientFitColumnIndex s d) =
      rawExteriorSupportFitColumn supportMatrix e row := by
  rfl

/-- The RHS entry is exactly the row-major serialized coefficient selected
by `RawCertificate`'s decoder. This is the shape/serialization boundary for
the later equation `fitMatrix * coefficients = rhs`. -/
theorem rawCoefficientFitRhs_entry {s : Nat} (raw : RawCoefficientArray)
    (row : IncreasingTriple (3 * s)) :
    rawCoefficientFitRhs raw row =
      raw[rawCoefficientOffset (3 * s) (increasingTripleI row)
        (increasingTripleJ row) (increasingTripleK row)]! := by
  rfl

/-- The selected serialized RHS coefficient is also the coefficient of the
alternating tensor decoded by `RawCertificate`. This bridge uses the existing
decoder theorem rather than assuming an interpretation of the full raw input
array. -/
theorem rawCoefficientFitRhs_eq_decoded {s : Nat} (raw : RawCoefficientArray)
    (row : IncreasingTriple (3 * s)) :
    rawCoefficientFitRhs raw row =
      encodeDenseInput (decodeRawArray (n := 3 * s) raw) row := by
  rw [rawCoefficientFitRhs, encode_decodeRawArray]

/-- Exact column-index cardinality target. The `Fin s` summand contributes
the `s` trace scalar unknowns; the second summand contributes one column for
each increasing triple of the serialized support dimension. -/
theorem rawCoefficientFitColumnIndex_card (s d : Nat) :
    Fintype.card (RawCoefficientFitColumnIndex s d) =
      s + Fintype.card (IncreasingTriple d) := by
  classical
  simp [RawCoefficientFitColumnIndex]

end CorruptedFieldRecovery
