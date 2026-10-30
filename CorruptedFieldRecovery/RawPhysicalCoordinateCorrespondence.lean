import CorruptedFieldRecovery.RawPhysicalPowerBasis

/-! Connect a physical block mask to the corresponding component of the
canonical quotient-field triple reconstructed from all three blocks. -/

namespace CorruptedFieldRecovery

open AdjoinRoot

/-- Select one component of a quotient-field triple in row-major order. -/
def rawFieldTripleComponent {K : Type*} (x : FieldTriple K) (block : Fin 3) : K :=
  if block = 0 then x.1 else if block = 1 then x.2.1 else x.2.2

/-- The exact Nat mask of a block denotes the matching component of the
canonical power-basis triple decoded from the full coordinate vector. -/
theorem rawPhysicalBlockMask_eq_canonicalComponent {s : Nat}
    (candidate : RawFieldCandidate s)
    (hcheck : rawFieldCandidateCheck candidate = true)
    (w : BinaryVector (3 * s)) (block : Fin 3) :
    rawCandidateQuotientClass candidate (rawPhysicalBlockMask w block) =
      rawFieldTripleComponent
        ((rawFieldTripleToBinaryVector (rawCandidateModulus candidate)
          (accepted_rawCandidateModulus_monic candidate hcheck)
          (by
            have hv := accepted_rawFieldCandidateCheck candidate hcheck
            have hm := rawFieldCandidateValid_modulus_polynomial candidate hv
            simpa [rawCandidateModulus] using hm.2)).symm w)
        block := by
  let p := rawCandidateModulus candidate
  have hv := accepted_rawFieldCandidateCheck candidate hcheck
  have hm := rawFieldCandidateValid_modulus_polynomial candidate hv
  have hd : p.natDegree = s := by simpa [p, rawCandidateModulus] using hm.2
  let hmnic := accepted_rawCandidateModulus_monic candidate hcheck
  let q := rawQuotientPowerCoordinates p hmnic hd
  let e := rawFieldTripleToBinaryVector p hmnic hd
  let coord := rawFieldTriplePowerCoordinates p hmnic hd
  have hcoord : q (rawFieldTripleComponent (e.symm w) block) =
      fun i => w (finProdFinEquiv (block, i)) := by
    funext i
    have hc := congrFun (coord.apply_symm_apply
      (fun ij => w (finProdFinEquiv ij))) (block, i)
    fin_cases block <;> exact hc
  calc
    rawCandidateQuotientClass candidate (rawPhysicalBlockMask w block) =
        q.symm (fun i => w (finProdFinEquiv (block, i))) := by
          simpa [q, p] using
            rawPhysicalBlockMask_eq_powerCoordinates candidate hcheck w block
    _ = rawFieldTripleComponent (e.symm w) block := by
          rw [← hcoord]
          exact q.symm_apply_apply _

end CorruptedFieldRecovery
