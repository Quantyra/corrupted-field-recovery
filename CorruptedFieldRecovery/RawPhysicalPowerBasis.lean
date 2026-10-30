import CorruptedFieldRecovery.RawPhysicalTraceBits
import CorruptedFieldRecovery.RawFieldCoordinateBridge

/-! Relate the little-endian block masks read from physical vectors to the
monomial expansion used by the accepted quotient-field power basis. -/

namespace CorruptedFieldRecovery

open Polynomial AdjoinRoot

/-- `ZMod 2` coefficients have exactly their expected Boolean encoding. -/
theorem rawZModTwo_boolValue (a : ZMod 2) :
    (if decide (a = 1) then (1 : ZMod 2) else 0) = a := by
  fin_cases a <;> decide

/-- A finite little-endian Bool vector expands to its coefficient monomials. -/
theorem rawBoolListPolynomial_ofFn {s : Nat} (bits : Fin s → Bool) :
    rawBoolListPolynomial (List.ofFn bits) =
      ∑ i : Fin s, Polynomial.monomial i (if bits i then (1 : ZMod 2) else 0) := by
  induction s with
  | zero => simp [List.ofFn, rawBoolListPolynomial]
  | succ s ih =>
      rw [List.ofFn_succ]
      have htail := ih (fun i => bits i.succ)
      simp only [rawBoolListPolynomial, htail, Fin.sum_univ_succ]
      rw [Finset.mul_sum]
      simp only [Polynomial.X_mul_monomial, Fin.val_succ]
      ac_rfl

/-- Polynomial interpretation of a physical coordinate block equals the
finite monomial sum of the corresponding vector entries. -/
theorem rawPhysicalBlockMask_polynomial {s : Nat}
    (v : BinaryVector (3 * s)) (block : Fin 3) :
    rawMaskPolynomial (rawPhysicalBlockMask v block) =
      ∑ i : Fin s,
        Polynomial.monomial i (v (finProdFinEquiv (block, i))) := by
  unfold rawPhysicalBlockMask
  rw [← rawBoolListPolynomial_eq_mask]
  rw [rawBoolListPolynomial_ofFn]
  apply Finset.sum_congr rfl
  intro i hi
  rw [rawZModTwo_boolValue]

/-- The quotient class of an extracted block mask is the quotient class of
its corresponding coefficient polynomial. -/
theorem rawPhysicalBlockMask_quotient {s : Nat}
    (candidate : RawFieldCandidate s) (v : BinaryVector (3 * s)) (block : Fin 3) :
    rawCandidateQuotientClass candidate (rawPhysicalBlockMask v block) =
      AdjoinRoot.mk (rawCandidateModulus candidate)
        (∑ i : Fin s,
          Polynomial.monomial i (v (finProdFinEquiv (block, i)))) := by
  rw [rawCandidateQuotientClass, rawPhysicalBlockMask_polynomial]

/-- The decoded component is the power-basis inverse of its exact physical
coefficient block. -/
theorem rawPhysicalBlockMask_eq_powerCoordinates {s : Nat}
    (candidate : RawFieldCandidate s)
    (hcheck : rawFieldCandidateCheck candidate = true)
    (v : BinaryVector (3 * s)) (block : Fin 3) :
    rawCandidateQuotientClass candidate (rawPhysicalBlockMask v block) =
      (rawQuotientPowerCoordinates (rawCandidateModulus candidate)
        (accepted_rawCandidateModulus_monic candidate hcheck)
        (by
          have hv := accepted_rawFieldCandidateCheck candidate hcheck
          have hm := rawFieldCandidateValid_modulus_polynomial candidate hv
          simpa [rawCandidateModulus] using hm.2)).symm
        (fun i => v (finProdFinEquiv (block, i))) := by
  rw [rawPhysicalBlockMask_quotient]
  let hdegree : (rawCandidateModulus candidate).natDegree = s := by
    have hv := accepted_rawFieldCandidateCheck candidate hcheck
    have hm := rawFieldCandidateValid_modulus_polynomial candidate hv
    simpa [rawCandidateModulus] using hm.2
  let b : Module.Basis (Fin s) (ZMod 2) (AdjoinRoot (rawCandidateModulus candidate)) :=
    (AdjoinRoot.powerBasisAux' (accepted_rawCandidateModulus_monic candidate hcheck)).reindex
      (finCongr hdegree)
  change AdjoinRoot.mk (rawCandidateModulus candidate)
      (∑ i : Fin s, Polynomial.monomial i (v (finProdFinEquiv (block, i)))) =
    b.equivFun.symm (fun i => v (finProdFinEquiv (block, i)))
  rw [Module.Basis.equivFun_symm_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hbi : b i = AdjoinRoot.mk (rawCandidateModulus candidate)
      (Polynomial.monomial i (1 : ZMod 2)) := by
    dsimp [b]
    rw [Module.Basis.reindex_apply]
    rw [AdjoinRoot.powerBasisAux']
    rw [Module.Basis.coe_ofEquivFun]
    let j : Fin (rawCandidateModulus candidate).natDegree := (finCongr hdegree).symm i
    change AdjoinRoot.mk (rawCandidateModulus candidate)
        (∑ x : Fin (rawCandidateModulus candidate).natDegree,
          Polynomial.monomial x
            ((Pi.single j (1 : ZMod 2) :
              Fin (rawCandidateModulus candidate).natDegree → ZMod 2) x)) =
      AdjoinRoot.mk (rawCandidateModulus candidate) (Polynomial.monomial i 1)
    apply congrArg (AdjoinRoot.mk (rawCandidateModulus candidate))
    rw [Finset.sum_eq_single j]
    · simp [j]
    · intro k hk hkj
      simp [hkj]
    · simp [j]
  rw [hbi]
  change AdjoinRoot.mk (rawCandidateModulus candidate)
      (Polynomial.monomial i (v (finProdFinEquiv (block, i)))) =
    (v (finProdFinEquiv (block, i))) •
      AdjoinRoot.mk (rawCandidateModulus candidate) (Polynomial.monomial i (1 : ZMod 2))
  calc
    _ = AdjoinRoot.mk (rawCandidateModulus candidate)
        (Polynomial.C (v (finProdFinEquiv (block, i))) *
          Polynomial.monomial i (1 : ZMod 2)) := by
          calc
            _ = AdjoinRoot.mk (rawCandidateModulus candidate)
                (Polynomial.monomial i
                  (v (finProdFinEquiv (block, i)) * 1)) := by simp
            _ = _ := by rw [Polynomial.C_mul_monomial]
    _ = AdjoinRoot.mk (rawCandidateModulus candidate)
          (Polynomial.C (v (finProdFinEquiv (block, i)))) *
        AdjoinRoot.mk (rawCandidateModulus candidate)
          (Polynomial.monomial i (1 : ZMod 2)) := map_mul _ _ _
    _ = (v (finProdFinEquiv (block, i))) •
          AdjoinRoot.mk (rawCandidateModulus candidate)
            (Polynomial.monomial i (1 : ZMod 2)) := by
          simp [Algebra.smul_def]

end CorruptedFieldRecovery
