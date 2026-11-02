import CorruptedFieldRecovery.RawCoefficientFitColumns
import CorruptedFieldRecovery.S010BalanceGaussianArrayDeterministicScan

/-! # Fin-indexed, zero-padded raw fit system

The compact source-indexed fit matrix has increasing-triple rows and
increasing-support-triple columns. This file embeds it into a fully
computable rectangular `Fin` matrix by enumerating *all* ordered triples and
zero-padding the non-increasing ones. This avoids a noncomputable `Fintype`
ordering and avoids searching coefficient vectors. The larger dimensions are
`(3*s)^3` rows and `s + d^3` coefficient columns, still polynomial in the
input dimensions.

The RHS is appended as one final column. The intended affine-solver criterion
is a null vector with final coordinate one; the corresponding equivalence is
recorded as a target below but is not proved in this draft. The deterministic
array scan is run on this augmented matrix. This module does not yet extract
that vector from the scan's free-kernel basis, nor prove the fit consistent
for manuscript inputs.
-/

namespace CorruptedFieldRecovery

/-- Computable lexicographic flattening of all ordered triples. The pair
equivalences preserve the declared `((i,j),k)` product order. -/
def rawOrderedTripleFinEquiv (n : Nat) :
    ((Fin n × Fin n) × Fin n) ≃ Fin ((n * n) * n) :=
  (Equiv.prodCongr finProdFinEquiv (Equiv.refl (Fin n))).trans finProdFinEquiv

/-- Finite column equivalence for the disjoint trace/support coordinates and
all ordered support triples. -/
def rawFitColumnFinEquiv (s d : Nat) :
    (Fin s ⊕ Fin ((d * d) * d)) ≃ Fin (s + (d * d) * d) :=
  finSumFinEquiv

/-- Finite column equivalence for appending the serialized RHS as the final
affine coordinate. -/
def rawFitAugmentedColumnFinEquiv (s d : Nat) :
    (Fin (s + (d * d) * d) ⊕ Fin 1) ≃ Fin ((s + (d * d) * d) + 1) :=
  finSumFinEquiv

/-- Decode a flattened row or support-column index to its ordered triple. -/
def rawOrderedTripleAt {n : Nat} (position : Fin ((n * n) * n)) :
    (Fin n × Fin n) × Fin n :=
  (rawOrderedTripleFinEquiv n).symm position

/-- Strictly increasing predicate for an ordered triple, matching
`IncreasingTriple`. -/
def rawOrderedTripleIncreasing {n : Nat}
    (triple : (Fin n × Fin n) × Fin n) : Prop :=
  triple.1.1 < triple.1.2 ∧ triple.1.2 < triple.2

/-- Turn a valid ordered triple into the source-indexed row type. -/
def rawOrderedTripleAsIncreasing {n : Nat}
    (triple : (Fin n × Fin n) × Fin n)
    (h : rawOrderedTripleIncreasing triple) : IncreasingTriple n :=
  ⟨triple, h⟩

/-- The compact source-indexed entry, flattened into every ordered physical
triple row and every ordered support-triple column. Invalid triples are
zero-padded. The flattening has no arbitrary or noncomputable ordering. -/
def rawCoefficientFitFiniteEntry {s d : Nat}
    (candidate : RawFieldCandidate s)
    (hcheck : rawFieldCandidateCheck candidate = true)
    (inverse : RawCoordinateMatrix) (supportMatrix : RawBinaryArray)
    (row : Fin (((3 * s) * (3 * s)) * (3 * s)))
    (column : Fin (s + (d * d) * d)) : ZMod 2 := by
  classical
  let triple := rawOrderedTripleAt row
  let columnTag := (rawFitColumnFinEquiv s d).symm column
  exact if hrow : rawOrderedTripleIncreasing triple then
      match columnTag with
      | Sum.inl j =>
          rawCoefficientFitEntry candidate hcheck inverse supportMatrix
            (rawOrderedTripleAsIncreasing triple hrow) (Sum.inl j)
      | Sum.inr e =>
          let supportTriple := rawOrderedTripleAt e
          if hsupport : rawOrderedTripleIncreasing supportTriple then
            rawCoefficientFitEntry candidate hcheck inverse supportMatrix
              (rawOrderedTripleAsIncreasing triple hrow)
              (Sum.inr (rawOrderedTripleAsIncreasing supportTriple hsupport))
          else 0
    else 0

/-- The same zero-padded ordered-triple embedding for the serialized RHS. -/
def rawCoefficientFitFiniteRhs {s : Nat} (raw : RawCoefficientArray)
    (row : Fin (((3 * s) * (3 * s)) * (3 * s))) : ZMod 2 := by
  classical
  let triple := rawOrderedTripleAt row
  exact if hrow : rawOrderedTripleIncreasing triple then
      rawCoefficientFitRhs raw (rawOrderedTripleAsIncreasing triple hrow)
    else 0

/-- The rectangular fit matrix in the exact `Fin` shape consumed by the
existing deterministic Gaussian scanner. Rows enumerate all ordered physical
triples; columns enumerate scalar positions followed by all ordered support
triples. Invalid increasing-triple positions are zero columns/rows. -/
def rawCoefficientFitFiniteMatrix {s d : Nat}
    (candidate : RawFieldCandidate s)
    (hcheck : rawFieldCandidateCheck candidate = true)
    (inverse : RawCoordinateMatrix) (supportMatrix : RawBinaryArray) :
    Matrix (Fin (((3 * s) * (3 * s)) * (3 * s)))
      (Fin (s + (d * d) * d)) (ZMod 2) :=
  fun row column =>
    rawCoefficientFitFiniteEntry candidate hcheck inverse supportMatrix row column

/-- Append the serialized data coefficient as the final column. A homogeneous
kernel vector with last coordinate one is an affine-fit solution over `F₂`. -/
def rawCoefficientFitAugmentedEntry {s d : Nat}
    (candidate : RawFieldCandidate s)
    (hcheck : rawFieldCandidateCheck candidate = true)
    (inverse : RawCoordinateMatrix) (supportMatrix : RawBinaryArray)
    (raw : RawCoefficientArray)
    (row : Fin (((3 * s) * (3 * s)) * (3 * s)))
    (column : Fin ((s + (d * d) * d) + 1)) : ZMod 2 :=
  match (rawFitAugmentedColumnFinEquiv s d).symm column with
  | Sum.inl coefficientColumn =>
      rawCoefficientFitFiniteEntry candidate hcheck inverse supportMatrix
        row coefficientColumn
  | Sum.inr _ => rawCoefficientFitFiniteRhs raw row

/-- The augmented coefficient-fit matrix. -/
def rawCoefficientFitAugmentedMatrix {s d : Nat}
    (candidate : RawFieldCandidate s)
    (hcheck : rawFieldCandidateCheck candidate = true)
    (inverse : RawCoordinateMatrix) (supportMatrix : RawBinaryArray)
    (raw : RawCoefficientArray) :
    Matrix (Fin (((3 * s) * (3 * s)) * (3 * s)))
      (Fin ((s + (d * d) * d) + 1)) (ZMod 2) :=
  fun row column =>
    rawCoefficientFitAugmentedEntry candidate hcheck inverse supportMatrix raw row column

/-- Exact affine meaning of the appended column: coefficients solve the
source-indexed fit precisely when the augmented matrix has a null vector
whose final coordinate is one. This is the proof target for the finite
matrix/array boundary; consistency itself is not assumed or proved here. -/
def RawCoefficientFitAffineSolution {s d : Nat}
    (candidate : RawFieldCandidate s)
    (hcheck : rawFieldCandidateCheck candidate = true)
    (inverse : RawCoordinateMatrix) (supportMatrix : RawBinaryArray)
    (raw : RawCoefficientArray) : Prop :=
  ∃ coefficients : RawCoefficientFitColumnIndex s d → ZMod 2,
    ∀ row : IncreasingTriple (3 * s),
      (∑ column : RawCoefficientFitColumnIndex s d,
        rawCoefficientFitEntry candidate hcheck inverse supportMatrix row column *
          coefficients column) = rawCoefficientFitRhs raw row

/-- Run the established deterministic nested-array scan on the augmented
finite matrix. This is the concrete elimination endpoint of this draft; a
subsequent bridge must select a free-kernel candidate with final coordinate
one and prove its coefficient slots solve `RawCoefficientFitAffineSolution`.
-/
def rawCoefficientFitAugmentedArrayRun {s d : Nat}
    (candidate : RawFieldCandidate s)
    (hcheck : rawFieldCandidateCheck candidate = true)
    (inverse : RawCoordinateMatrix) (supportMatrix : RawBinaryArray)
    (raw : RawCoefficientArray) :=
  let matrix := rawCoefficientFitAugmentedMatrix candidate hcheck inverse
    supportMatrix raw
  let cells := Array.ofFn fun row : Fin (((3 * s) * (3 * s)) * (3 * s)) =>
    Array.ofFn fun column : Fin ((s + (d * d) * d) + 1) => matrix row column
  actualBalanceGaussianArrayColumnScan cells (∅ : Finset (Fin (((3 * s) * (3 * s)) * (3 * s))))
    (List.ofFn fun column : Fin ((s + (d * d) * d) + 1) => column)

/-- The matrix-to-array view of the executed scan starts at exactly the
augmented fit matrix. This pins down the row-major solver input rather than
only specifying an abstract array shape. -/
theorem rawCoefficientFitAugmentedArrayRun_refines {s d : Nat}
    (candidate : RawFieldCandidate s)
    (hcheck : rawFieldCandidateCheck candidate = true)
    (inverse : RawCoordinateMatrix) (supportMatrix : RawBinaryArray)
    (raw : RawCoefficientArray) :
    (actualBalanceGaussianArrayView
        (rawCoefficientFitAugmentedArrayRun candidate hcheck inverse supportMatrix raw).1,
      (rawCoefficientFitAugmentedArrayRun candidate hcheck inverse supportMatrix raw).2) =
      balanceGaussianColumnScan
        (rawCoefficientFitAugmentedMatrix candidate hcheck inverse supportMatrix raw)
        ∅ (List.ofFn fun column : Fin ((s + (d * d) * d) + 1) => column) := by
  classical
  unfold rawCoefficientFitAugmentedArrayRun
  simpa [actualBalanceGaussianArrayView] using
    actualBalanceGaussianArrayColumnScan_refines
      (Array.ofFn fun row : Fin (((3 * s) * (3 * s)) * (3 * s)) =>
        Array.ofFn fun column : Fin ((s + (d * d) * d) + 1) =>
          rawCoefficientFitAugmentedMatrix candidate hcheck inverse supportMatrix raw
            row column)
      ∅ (List.ofFn fun column : Fin ((s + (d * d) * d) + 1) => column)

end CorruptedFieldRecovery
