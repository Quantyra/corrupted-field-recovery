import CorruptedFieldRecovery.S010BalanceGaussianRawSolverBridge

open scoped Matrix

namespace CorruptedFieldRecovery

/-- The proof-level sums over the scan's free-index subtype use classical
finite enumeration. The executable output remains the explicit filtered list
`actualBalanceGaussianRawFreeColumns`; this instance is only used to state and
prove finite linear combinations and spanning theorems. -/
noncomputable instance actualBalanceGaussianFreeIndexFintype
    {m n : Nat} (pivots : List (Fin m × Fin n)) :
    Fintype (balanceGaussianFreeIndex pivots) := by
  classical
  exact Subtype.fintype _

/-- Turn a row-major coefficient vector into the linear endomorphism whose
matrix has those coefficients. This is a direct finite sum, so candidate
construction does not call a noncomputable basis representation. -/
def actualBalanceGaussianEndFromCoordinates {s : Nat}
    (x : Fin ((3 * s) * (3 * s)) → ZMod 2) :
    Module.End (ZMod 2) (BinaryVector (3 * s)) where
  toFun v := fun i =>
    ∑ j : Fin (3 * s),
      x (actualBalanceGaussianColumnEquiv s (i, j)) * v j
  map_add' v w := by
    funext i
    simp only [Pi.add_apply, Finset.sum_add_distrib, mul_add]
  map_smul' a v := by
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    calc
      (∑ j : Fin (3 * s),
          x (actualBalanceGaussianColumnEquiv s (i, j)) * (a * v j)) =
        ∑ j : Fin (3 * s), a *
          (x (actualBalanceGaussianColumnEquiv s (i, j)) * v j) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = a * ∑ j : Fin (3 * s),
          x (actualBalanceGaussianColumnEquiv s (i, j)) * v j := by
            rw [Finset.mul_sum]

/-- Reading matrix entries back from the explicit endomorphism recovers every
input coordinate. -/
theorem actualBalanceGaussianInputCoordinates_endFromCoordinates {s : Nat}
    (x : Fin ((3 * s) * (3 * s)) → ZMod 2) :
    actualBalanceGaussianInputCoordinates
      (actualBalanceGaussianEndFromCoordinates x) = x := by
  funext column
  let pair := (actualBalanceGaussianColumnEquiv s).symm column
  change actualBalanceMatrixEntry
      (actualBalanceGaussianEndFromCoordinates x) pair.1 pair.2 = x column
  simp [actualBalanceMatrixEntry, actualBalanceGaussianEndFromCoordinates,
    actualBalanceUnitVector, pair]

/-- The explicit endomorphism constructor is injective, witnessed by its
computable matrix-entry coordinates. -/
theorem actualBalanceGaussianEndFromCoordinates_injective {s : Nat}
    {x y : Fin ((3 * s) * (3 * s)) → ZMod 2}
    (h : actualBalanceGaussianEndFromCoordinates x =
      actualBalanceGaussianEndFromCoordinates y) : x = y := by
  have hcoords := congrArg actualBalanceGaussianInputCoordinates h
  simpa only [actualBalanceGaussianInputCoordinates_endFromCoordinates] using hcoords

/-- The coordinate constructor is linear in the coefficient vector. -/
def actualBalanceGaussianEndFromCoordinatesLinearMap {s : Nat} :
    (Fin ((3 * s) * (3 * s)) → ZMod 2) →ₗ[ZMod 2]
      Module.End (ZMod 2) (BinaryVector (3 * s)) where
  toFun := actualBalanceGaussianEndFromCoordinates
  map_add' x y := by
    ext v i
    simp [actualBalanceGaussianEndFromCoordinates,
      Finset.sum_add_distrib, add_mul]
  map_smul' a x := by
    apply LinearMap.ext
    intro v
    funext i
    simp only [actualBalanceGaussianEndFromCoordinates,
      Pi.smul_apply, smul_eq_mul]
    calc
      (∑ j : Fin (3 * s),
          (a * x (actualBalanceGaussianColumnEquiv s (i, j))) * v j) =
        ∑ j : Fin (3 * s), a *
          (x (actualBalanceGaussianColumnEquiv s (i, j)) * v j) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = a * ∑ j : Fin (3 * s),
          x (actualBalanceGaussianColumnEquiv s (i, j)) * v j := by
            rw [Finset.mul_sum]

/-- The explicit constructor and matrix-entry reader are inverse on physical
endomorphisms. The basis representation appears only in this proof-level
identity; the finite-array candidate builder itself remains computable. -/
theorem actualBalanceGaussianEndFromCoordinates_inputCoordinates {s : Nat}
    (T : Module.End (ZMod 2) (BinaryVector (3 * s))) :
    actualBalanceGaussianEndFromCoordinates
      (actualBalanceGaussianInputCoordinates T) = T := by
  apply (actualBalanceEndBasis s).repr.injective
  ext pair
  have hleft := actualBalanceGaussianInputCoordinates_pair
    (actualBalanceGaussianEndFromCoordinates
      (actualBalanceGaussianInputCoordinates T))
  have hright := actualBalanceGaussianInputCoordinates_pair T
  calc
    (actualBalanceEndBasis s).repr
        (actualBalanceGaussianEndFromCoordinates
          (actualBalanceGaussianInputCoordinates T)) pair =
      actualBalanceGaussianInputCoordinates
        (actualBalanceGaussianEndFromCoordinates
          (actualBalanceGaussianInputCoordinates T))
        (actualBalanceGaussianColumnEquiv s pair) :=
          (congrFun hleft pair).symm
    _ = actualBalanceGaussianInputCoordinates T
        (actualBalanceGaussianColumnEquiv s pair) := by
          rw [actualBalanceGaussianInputCoordinates_endFromCoordinates]
    _ = (actualBalanceEndBasis s).repr T pair := congrFun hright pair

/-- The raw solver's free-column family, interpreted as actual physical
endomorphisms by the explicit coordinate constructor. -/
def actualBalanceGaussianRawCandidateFamily {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s) :
    balanceGaussianFreeIndex (actualBalanceGaussianRawScan raw tape).2 →
      Module.End (ZMod 2) (BinaryVector (3 * s)) :=
  fun free => actualBalanceGaussianEndFromCoordinates
    (balanceGaussianFreeCandidateFamily
      (actualBalanceGaussianRawScan raw tape).1
      (actualBalanceGaussianRawScan raw tape).2 free)

/-- Every candidate generated by the raw deterministic scan is in the kernel
of its actual coefficient matrix. This derives membership from recorded unit
pivots, distinct pivot rows, and the zero-unused-row theorem. -/
theorem actualBalanceGaussianRawCandidate_mem_ker {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s)
    (free : balanceGaussianFreeIndex (actualBalanceGaussianRawScan raw tape).2) :
    (actualBalanceGaussianRawScan raw tape).1 *ᵥ
      balanceGaussianFreeCandidateFamily
        (actualBalanceGaussianRawScan raw tape).1
        (actualBalanceGaussianRawScan raw tape).2 free = 0 := by
  let A := actualBalanceGaussianRawMatrix raw tape
  let columns := List.ofFn (fun j : Fin ((3 * s) * (3 * s)) => j)
  let run := balanceGaussianColumnScan A ∅ columns
  have hrows : (run.2.map Prod.fst).Nodup := by
    simpa [run, columns] using
      balanceGaussianColumnScan_pivotRows_nodup columns A ∅
  have hunit : ∀ pivot ∈ run.2, ∀ i,
      run.1 i pivot.2 = if i = pivot.1 then 1 else 0 := by
    intro pivot hpivot i
    exact balanceGaussianColumnScan_recordedPivots_unit
      columns A ∅ pivot (by simpa [run] using hpivot) i
  have hzero : ∀ i, i ∉ run.2.map Prod.fst → run.1 i = 0 := by
    intro i hi
    funext column
    exact balanceGaussianFullColumnScan_unusedRows_zero A i (by
      simpa [run, columns] using hi) column
  have hcandidate := balanceGaussianFreeKernelCandidate_mem_ker
    run.1 run.2 free.1 free.2 hrows hunit (by
      intro i hi
      exact congrFun (hzero i hi) free.1)
  simpa [A, columns, run, actualBalanceGaussianRawScan] using hcandidate

/-- The candidate endomorphisms satisfy the manuscript's actual four-slot
physical balance equations on the decoded raw input. -/
theorem actualBalanceGaussianRawCandidate_balanced {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s)
    (free : balanceGaussianFreeIndex (actualBalanceGaussianRawScan raw tape).2) :
    actualFourBilinearBalanced (decodeRawArray (n := 3 * s) raw) tape
      (actualBalanceGaussianRawCandidateFamily raw tape free) := by
  have hcoords := actualBalanceGaussianInputCoordinates_endFromCoordinates
    (balanceGaussianFreeCandidateFamily
      (actualBalanceGaussianRawScan raw tape).1
      (actualBalanceGaussianRawScan raw tape).2 free)
  have hraw := (balanceGaussianColumnScan_kernel_iff
    (List.ofFn (fun j : Fin ((3 * s) * (3 * s)) => j))
    (actualBalanceGaussianRawMatrix raw tape) ∅
    (balanceGaussianFreeCandidateFamily
      (actualBalanceGaussianRawScan raw tape).1
      (actualBalanceGaussianRawScan raw tape).2 free)).mp
    (actualBalanceGaussianRawCandidate_mem_ker raw tape free)
  have hphysical : actualBalanceGaussianRawMatrix raw tape *ᵥ
      actualBalanceGaussianInputCoordinates
        (actualBalanceGaussianRawCandidateFamily raw tape free) = 0 := by
    change actualBalanceGaussianRawMatrix raw tape *ᵥ
      actualBalanceGaussianInputCoordinates
        (actualBalanceGaussianEndFromCoordinates
          (balanceGaussianFreeCandidateFamily
            (actualBalanceGaussianRawScan raw tape).1
            (actualBalanceGaussianRawScan raw tape).2 free)) = 0
    rw [hcoords]
    exact hraw
  exact (actualBalanceGaussianRawMatrix_solution_iff raw tape
    (actualBalanceGaussianRawCandidateFamily raw tape free)).mp hphysical

/-- The executable scan's free-coordinate candidates reconstruct every
solution of the reindexed raw balance system. The sum coefficients are the
solution's own free-column entries. -/
theorem actualBalanceGaussianRawScan_reconstruct {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s) :
    ∀ x : Fin ((3 * s) * (3 * s)) → ZMod 2,
      (actualBalanceGaussianRawScan raw tape).1 *ᵥ x = 0 →
      x = ∑ free : balanceGaussianFreeIndex
          (actualBalanceGaussianRawScan raw tape).2,
        x free.1 • balanceGaussianFreeCandidateFamily
          (actualBalanceGaussianRawScan raw tape).1
          (actualBalanceGaussianRawScan raw tape).2 free := by
  simpa [actualBalanceGaussianRawScan] using
    balanceGaussianFullColumnScan_candidates_reconstruct
      (actualBalanceGaussianRawMatrix raw tape)

/-- Every physically balanced endomorphism is represented by the explicit
free-column candidate expansion in coefficient coordinates. -/
theorem actualBalanceGaussianRawBalanced_coordinates_reconstruct {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s)
    (T : Module.End (ZMod 2) (BinaryVector (3 * s)))
    (hbalanced : actualFourBilinearBalanced
      (decodeRawArray (n := 3 * s) raw) tape T) :
    actualBalanceGaussianInputCoordinates T =
      ∑ free : balanceGaussianFreeIndex
          (actualBalanceGaussianRawScan raw tape).2,
        actualBalanceGaussianInputCoordinates T free.1 •
          balanceGaussianFreeCandidateFamily
            (actualBalanceGaussianRawScan raw tape).1
            (actualBalanceGaussianRawScan raw tape).2 free := by
  apply actualBalanceGaussianRawScan_reconstruct
  exact (balanceGaussianColumnScan_kernel_iff
    (List.ofFn (fun j : Fin ((3 * s) * (3 * s)) => j))
    (actualBalanceGaussianRawMatrix raw tape) ∅
    (actualBalanceGaussianInputCoordinates T)).2
    ((actualBalanceGaussianRawMatrix_solution_iff raw tape T).mpr hbalanced)

/-- The reconstructed coefficient expansion is also an equality of actual
physical endomorphisms. Thus the scan returns a spanning family for all
endomorphisms satisfying the decoded raw balance equations. -/
theorem actualBalanceGaussianRawBalanced_endomorphism_reconstruct {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s)
    (T : Module.End (ZMod 2) (BinaryVector (3 * s)))
    (hbalanced : actualFourBilinearBalanced
      (decodeRawArray (n := 3 * s) raw) tape T) :
    T = ∑ free : balanceGaussianFreeIndex
          (actualBalanceGaussianRawScan raw tape).2,
        actualBalanceGaussianInputCoordinates T free.1 •
          actualBalanceGaussianRawCandidateFamily raw tape free := by
  have hcoords := actualBalanceGaussianRawBalanced_coordinates_reconstruct
    raw tape T hbalanced
  calc
    T = actualBalanceGaussianEndFromCoordinates
        (actualBalanceGaussianInputCoordinates T) :=
          (actualBalanceGaussianEndFromCoordinates_inputCoordinates T).symm
    _ = actualBalanceGaussianEndFromCoordinates
          (∑ free : balanceGaussianFreeIndex
            (actualBalanceGaussianRawScan raw tape).2,
            actualBalanceGaussianInputCoordinates T free.1 •
              balanceGaussianFreeCandidateFamily
                (actualBalanceGaussianRawScan raw tape).1
                (actualBalanceGaussianRawScan raw tape).2 free) :=
          congrArg actualBalanceGaussianEndFromCoordinates hcoords
    _ = ∑ free : balanceGaussianFreeIndex
          (actualBalanceGaussianRawScan raw tape).2,
        actualBalanceGaussianInputCoordinates T free.1 •
          actualBalanceGaussianRawCandidateFamily raw tape free := by
          change actualBalanceGaussianEndFromCoordinatesLinearMap
            (∑ free : balanceGaussianFreeIndex
              (actualBalanceGaussianRawScan raw tape).2,
              actualBalanceGaussianInputCoordinates T free.1 •
                balanceGaussianFreeCandidateFamily
                  (actualBalanceGaussianRawScan raw tape).1
                  (actualBalanceGaussianRawScan raw tape).2 free) = _
          simp [actualBalanceGaussianRawCandidateFamily,
            actualBalanceGaussianEndFromCoordinatesLinearMap,
            map_sum, map_smul]

/-- Under the declared dense-array size condition, every executable raw
candidate passes the manuscript's finite balance checker. -/
theorem actualBalanceGaussianRawCandidate_checker_true {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s)
    (hsize : raw.size = (3 * s) * (3 * s) * (3 * s))
    (free : balanceGaussianFreeIndex (actualBalanceGaussianRawScan raw tape).2) :
    actualBalanceRawInputConstraintCheck raw tape
      (actualBalanceGaussianRawCandidateFamily raw tape free) = true := by
  apply (actualBalanceRawInputConstraintCheck_iff raw tape
    (actualBalanceGaussianRawCandidateFamily raw tape free)).2
  exact ⟨hsize, actualBalanceGaussianRawCandidate_balanced raw tape free⟩

/-- The endomorphisms emitted in list order by the executable free-column
enumerator. -/
def actualBalanceGaussianRawCandidateEndList {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s) :
    List (Module.End (ZMod 2) (BinaryVector (3 * s))) :=
  (actualBalanceGaussianRawFreeColumns raw tape).map fun free =>
    actualBalanceGaussianEndFromCoordinates
      (balanceGaussianFreeKernelCandidate
        (actualBalanceGaussianRawScan raw tape).1
        (actualBalanceGaussianRawScan raw tape).2 free)

/-- Every endomorphism in the executable candidate list satisfies the actual
physical balance equations. The proof extracts the nonpivot condition from
the finite filter, then invokes the scan-derived candidate theorem. -/
theorem actualBalanceGaussianRawCandidateEndList_balanced {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s)
    {T : Module.End (ZMod 2) (BinaryVector (3 * s))}
    (hT : T ∈ actualBalanceGaussianRawCandidateEndList raw tape) :
    actualFourBilinearBalanced (decodeRawArray (n := 3 * s) raw) tape T := by
  rcases List.mem_map.mp hT with ⟨column, hcolumn, rfl⟩
  have hfilter := List.mem_filter.mp hcolumn
  have hfree : column ∉ (actualBalanceGaussianRawScan raw tape).2.map Prod.snd :=
    of_decide_eq_true hfilter.2
  let free : balanceGaussianFreeIndex (actualBalanceGaussianRawScan raw tape).2 :=
    ⟨column, hfree⟩
  simpa [actualBalanceGaussianRawCandidateFamily, free] using
    actualBalanceGaussianRawCandidate_balanced raw tape free

/-- The returned candidate family is linearly independent in coefficient
space; together with candidate balance and coordinate reconstruction this is
the explicit kernel-basis bridge for the raw input. -/
theorem actualBalanceGaussianRawCandidates_linearIndependent {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s) :
    LinearIndependent (ZMod 2)
      (balanceGaussianFreeCandidateFamily
        (actualBalanceGaussianRawScan raw tape).1
        (actualBalanceGaussianRawScan raw tape).2) := by
  classical
  exact balanceGaussianFreeCandidateFamily_linearIndependent _ _

/-- The corresponding physical endomorphisms are also linearly independent:
the explicit coordinate constructor is injective and carries the coefficient
candidate family to this family. -/
theorem actualBalanceGaussianRawCandidateFamily_linearIndependent {s : Nat}
    (raw : RawCoefficientArray) (tape : FiveWordTape s) :
    LinearIndependent (ZMod 2)
      (actualBalanceGaussianRawCandidateFamily raw tape) := by
  let F := actualBalanceGaussianEndFromCoordinatesLinearMap (s := s)
  have hF : Function.Injective F := by
    intro x y h
    change actualBalanceGaussianEndFromCoordinates x =
      actualBalanceGaussianEndFromCoordinates y at h
    exact actualBalanceGaussianEndFromCoordinates_injective h
  have hker : LinearMap.ker F = ⊥ := LinearMap.ker_eq_bot.mpr hF
  have hcoord := actualBalanceGaussianRawCandidates_linearIndependent raw tape
  have hmap := hcoord.map' F hker
  simpa [F, Function.comp_def, actualBalanceGaussianRawCandidateFamily,
    actualBalanceGaussianEndFromCoordinatesLinearMap] using hmap

end CorruptedFieldRecovery
