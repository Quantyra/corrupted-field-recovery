import CorruptedFieldRecovery.RawRabinScanBitCost
import CorruptedFieldRecovery.RawRabinCandidateCorrectness

/-! Short-circuit cost instrumentation for the actual `List.range` Rabin scan
and its connection to the candidate-level Boolean gate. -/

namespace CorruptedFieldRecovery

/-- Costed `List.all` execution for the exact per-degree Rabin predicate.
The tail is evaluated only when the current check succeeds. -/
def rawRabinCheckListBitCosted (modulus : Nat) : List Nat → Bool × Nat
  | [] => (true, 0)
  | i :: is =>
      let step := rawRabinCheckIndexBitCosted modulus (i + 1)
      if step.1 then
        let rest := rawRabinCheckListBitCosted modulus is
        (rest.1, step.2 + rest.2)
      else (false, step.2)

/-- The short-circuit instrumentation preserves the exact list predicate. -/
theorem rawRabinCheckListBitCosted_fst (modulus : Nat) (indices : List Nat) :
    (rawRabinCheckListBitCosted modulus indices).1 =
      indices.all (fun i => decide
        (rawPolynomialGcd modulus
          (Nat.xor (rawCandidateFrobeniusAux modulus (i + 1) 2) 2) = 1)) := by
  induction indices with
  | nil => simp [rawRabinCheckListBitCosted]
  | cons i is ih =>
      simp only [rawRabinCheckListBitCosted]
      rw [rawRabinCheckIndexBitCosted_fst, ih]
      rw [List.all_cons]
      cases hpred : decide
          (rawPolynomialGcd modulus
            (Nat.xor (rawCandidateFrobeniusAux modulus (i + 1) 2) 2) = 1) <;>
        simp

/-- The candidate-level costed scan evaluates the same `List.range` and
per-degree predicates as `rawCandidateRabinCheck`. -/
def rawCandidateRabinCheckBitCosted {s : Nat}
    (candidate : RawFieldCandidate s) : Bool × Nat :=
  rawRabinCheckListBitCosted (rawFieldBitsToNat candidate.modulus)
    (List.range (s / 2))

theorem rawCandidateRabinCheckBitCosted_fst {s : Nat}
    (candidate : RawFieldCandidate s) :
    (rawCandidateRabinCheckBitCosted candidate).1 =
      rawCandidateRabinCheck candidate := by
  unfold rawCandidateRabinCheckBitCosted
  rw [rawRabinCheckListBitCosted_fst]
  rfl

/-- Uniform declared charge for one tested degree when the tested exponent is
at most `q` and all mask states are bounded by `W` bits. -/
def rawRabinScanUniformCharge (W q : Nat) : Nat :=
  q * rawRabinFrobeniusStepCharge W +
    (2 * W + 2) *
      (40 * (3 * (2 * W) + 6) ^ 2 * (2 * W + 1)) + 4 * W

/-- The actual short-circuit list evaluator costs at most list length times a
uniform bound. This theorem accounts for the skipped suffix after a failed
Boolean check. -/
theorem rawRabinCheckListBitCosted_cost_le
    {modulus W q : Nat} (hmod : modulus ≠ 0) (hmodOne : 1 < modulus)
    (hmodWidth : modulus < 2 ^ W) (hW : 2 ≤ W)
    (indices : List Nat) (hindices : ∀ i, i ∈ indices → i + 1 ≤ q) :
    (rawRabinCheckListBitCosted modulus indices).2 ≤
      indices.length * rawRabinScanUniformCharge W q := by
  induction indices with
  | nil => simp [rawRabinCheckListBitCosted]
  | cons i is ih =>
      have hi := hindices i (by simp)
      have htail : ∀ j, j ∈ is → j + 1 ≤ q := by
        intro j hj
        exact hindices j (by simp [hj])
      have hstep := rawRabinCheckIndexBitCosted_cost_le
        hmod hmodOne hmodWidth hW (d := i + 1)
      have hstepUniform :
          (rawRabinCheckIndexBitCosted modulus (i + 1)).2 ≤
            rawRabinScanUniformCharge W q := by
        have hstep' :
            (rawRabinCheckIndexBitCosted modulus (i + 1)).2 ≤
              (i + 1) * rawRabinFrobeniusStepCharge W +
                (2 * W + 2) *
                  (40 * (3 * (2 * W) + 6) ^ 2 * (2 * W + 1)) + 4 * W := by
          simpa [rawRabinCheckIndexCharge] using hstep
        unfold rawRabinScanUniformCharge
        have hmult := Nat.mul_le_mul_right
          (rawRabinFrobeniusStepCharge W) hi
        nlinarith [hstep']
      have hrest := ih htail
      by_cases hsuccess :
          (rawRabinCheckIndexBitCosted modulus (i + 1)).1 = true
      · simp [rawRabinCheckListBitCosted, hsuccess]
        calc
          _ ≤ rawRabinScanUniformCharge W q +
              is.length * rawRabinScanUniformCharge W q :=
                Nat.add_le_add hstepUniform hrest
          _ = (is.length + 1) * rawRabinScanUniformCharge W q := by
                rw [Nat.succ_mul]
                omega
      · simp [rawRabinCheckListBitCosted, hsuccess]
        calc
          _ ≤ rawRabinScanUniformCharge W q := hstepUniform
          _ ≤ rawRabinScanUniformCharge W q +
              is.length * rawRabinScanUniformCharge W q := by omega
          _ = (is.length + 1) * rawRabinScanUniformCharge W q := by
                rw [Nat.succ_mul]
                omega

/-- The short-circuit executable candidate scan has a polynomial declared
charge under the candidate modulus shape invariant. -/
theorem rawCandidateRabinCheckBitCosted_cost_le {s : Nat}
    (candidate : RawFieldCandidate s)
    (hshape : rawFieldCandidateShapeCheck candidate = true) :
    (rawCandidateRabinCheckBitCosted candidate).2 ≤
      (s / 2) * rawRabinScanUniformCharge (s + 1) (s / 2) := by
  rcases (rawFieldCandidateShapeCheck_iff candidate).mp hshape with
    ⟨hs, hsize, htop, _, _⟩
  have hlength : candidate.modulus.toList.length = s + 1 := by
    simpa using hsize
  have hmaskUpper := rawBitsToNat_lt_pow_length candidate.modulus.toList
  have hmodWidth : rawFieldBitsToNat candidate.modulus < 2 ^ (s + 1) := by
    simpa [rawFieldBitsToNat, hlength] using hmaskUpper
  have hmodLower : 2 ^ s ≤ rawFieldBitsToNat candidate.modulus := by
    by_contra h
    have hlt : rawFieldBitsToNat candidate.modulus < 2 ^ s := Nat.lt_of_not_ge h
    have htop' := htop
    rw [Nat.div_eq_of_lt hlt] at htop'
    norm_num at htop'
  have hmodOne : 1 < rawFieldBitsToNat candidate.modulus := by
    have hp : 2 ≤ 2 ^ s := by
      have hpow : 2 ^ 1 ≤ 2 ^ s :=
        Nat.pow_le_pow_right (by decide : 0 < 2) hs
      simpa using hpow
    omega
  have hcost := rawRabinCheckListBitCosted_cost_le
    (modulus := rawFieldBitsToNat candidate.modulus)
    (W := s + 1) (q := s / 2)
    (by omega : rawFieldBitsToNat candidate.modulus ≠ 0)
    hmodOne hmodWidth (by omega : 2 ≤ s + 1)
    (List.range (s / 2)) (by
      intro i hi
      have hi' : i < s / 2 := by simpa using hi
      omega)
  simpa [rawCandidateRabinCheckBitCosted, rawRabinScanUniformCharge] using hcost

end CorruptedFieldRecovery
