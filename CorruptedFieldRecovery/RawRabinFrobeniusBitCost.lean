import CorruptedFieldRecovery.RawRabinGcdBitCostBounds

/-! Charge and representative-width bounds for the actual repeated-square
Frobenius loop used by the fast Rabin scan. -/

namespace CorruptedFieldRecovery

/-- One declared charge for a Frobenius iteration: grade-school mask
multiplication, bounded mask reduction, and loop/control width charges. -/
def rawRabinFrobeniusStepCharge (W : Nat) : Nat :=
  8 * (2 * W + 2) * (W + 1) +
    (2 * W) * (40 * (4 * W + 4) ^ 2) + 2 * W

/-- Costed repeated quotient squaring. The first component follows the same
square/remainder loop as `rawCandidateFrobeniusAux`; the second accumulates the
declared multiplication, remainder, and control-width charges. -/
def rawCandidateFrobeniusAuxBitCosted (modulus : Nat) : Nat → Nat → Nat × Nat
  | 0, x => (x, 0)
  | d + 1, x =>
      let square := rawPolyMulBitCosted x x
      let rem := rawPolynomialRemainderBitCosted square.1 modulus
      let rest := rawCandidateFrobeniusAuxBitCosted modulus d rem.1
      (rest.1, square.2 + rem.2 + rawNatBitWidth modulus +
        rawNatBitWidth x + rest.2)

/-- The cost instrumentation returns exactly the executable Frobenius mask. -/
theorem rawCandidateFrobeniusAuxBitCosted_fst (modulus d x : Nat) :
    (rawCandidateFrobeniusAuxBitCosted modulus d x).1 =
      rawCandidateFrobeniusAux modulus d x := by
  induction d generalizing x with
  | zero => simp [rawCandidateFrobeniusAuxBitCosted, rawCandidateFrobeniusAux]
  | succ d ih =>
      dsimp [rawCandidateFrobeniusAuxBitCosted, rawCandidateFrobeniusAux]
      rw [rawPolyMulBitCosted_fst, rawPolynomialRemainderBitCosted_fst]
      exact ih _

/-- Under a common W-bit bound on the modulus and current representative, each
Frobenius iteration keeps its reduced representative W-bit. The intermediate
square is bounded by 2W bits. -/
theorem rawCandidateFrobeniusAuxBitCosted_lt_pow
    {modulus d x W : Nat} (hmod : modulus ≠ 0)
    (hmodWidth : modulus < 2 ^ W) (hx : x < 2 ^ W) :
    (rawCandidateFrobeniusAuxBitCosted modulus d x).1 < 2 ^ W := by
  induction d generalizing x with
  | zero => simpa [rawCandidateFrobeniusAuxBitCosted] using hx
  | succ d ih =>
      let square := rawPolyMulBitCosted x x
      let rem := rawPolynomialRemainderBitCosted square.1 modulus
      have hrem : rem.1 < 2 ^ W := by
        rw [show rem.1 = rawPolynomialRemainder square.1 modulus by
          dsimp [rem]
          exact rawPolynomialRemainderBitCosted_fst square.1 modulus]
        exact lt_trans (rawPolynomialRemainder_lt hmod) hmodWidth
      simpa [rawCandidateFrobeniusAuxBitCosted, square, rem] using ih hrem

/-- The actual costed repeated-square loop has a cubic-in-W declared charge
per Frobenius step. The proof uses the grade-school multiplication bound, the
remainder evaluator's cost theorem, and the proved W-bit representative
invariant. This is a bound on the declared recurrence, not machine runtime. -/
theorem rawCandidateFrobeniusAuxBitCosted_cost_le
    {modulus d x W : Nat} (hmod : modulus ≠ 0)
    (hmodOne : 1 < modulus) (hmodWidth : modulus < 2 ^ W)
    (hW : 0 < W) (hx : x < 2 ^ W) :
    (rawCandidateFrobeniusAuxBitCosted modulus d x).2 ≤
      d * rawRabinFrobeniusStepCharge W := by
  induction d generalizing x with
  | zero => simp [rawCandidateFrobeniusAuxBitCosted]
  | succ d ih =>
      let square := rawPolyMulBitCosted x x
      let rem := rawPolynomialRemainderBitCosted square.1 modulus
      have hsquare : square.1 < 2 ^ (2 * W) := by
        have hmul := rawPolyMul_lt_pow W W x x hx hx
        rw [show square.1 = rawPolyMul x x by
          dsimp [square]
          exact rawPolyMulBitCosted_fst x x]
        simpa [two_mul, Nat.add_comm] using hmul
      have hremWidth : rem.1 < 2 ^ W := by
        rw [show rem.1 = rawPolynomialRemainder square.1 modulus by
          dsimp [rem]
          exact rawPolynomialRemainderBitCosted_fst square.1 modulus]
        exact lt_trans (rawPolynomialRemainder_lt hmod) hmodWidth
      have hmulCost := rawPolyMulBitCosted_cost_le hx hx
      have hlogMod : Nat.log2 modulus < W := rawLog2_lt_of_lt_pow hW hmodWidth
      have hwidthMod : rawNatBitWidth modulus ≤ W := by
        unfold rawNatBitWidth
        omega
      have hwidthLog : rawNatBitWidth (Nat.log2 modulus) ≤ W := by
        have hloglog : Nat.log2 (Nat.log2 modulus) ≤ Nat.log2 modulus :=
          Nat.log2_le_self _
        unfold rawNatBitWidth
        omega
      have hterm : 2 * W + Nat.log2 modulus +
          rawNatBitWidth (Nat.log2 modulus) + 4 ≤ 4 * W + 4 := by omega
      have hquad : 40 * (2 * W + Nat.log2 modulus +
          rawNatBitWidth (Nat.log2 modulus) + 4) ^ 2 ≤
          40 * (4 * W + 4) ^ 2 := by
        gcongr
      have hremCost := rawPolynomialRemainderBitCosted_cost_le
        (A := 2 * W) (dividend := square.1) (divisor := modulus)
        (by omega) hsquare hmodOne
      have hremCost' : rem.2 ≤ (2 * W) * (40 * (4 * W + 4) ^ 2) := by
        have hremCost'' : rem.2 ≤ (2 * W) *
            (40 * (2 * W + Nat.log2 modulus +
              rawNatBitWidth (Nat.log2 modulus) + 4) ^ 2) := by
          simpa [rem] using hremCost
        exact le_trans hremCost'' (Nat.mul_le_mul_left (2 * W) hquad)
      have hwidthX : rawNatBitWidth x ≤ W := by
        unfold rawNatBitWidth
        have hlogX := rawLog2_lt_of_lt_pow hW hx
        omega
      have hlocal : square.2 + rem.2 + rawNatBitWidth modulus +
          rawNatBitWidth x ≤ rawRabinFrobeniusStepCharge W := by
        unfold rawRabinFrobeniusStepCharge
        have hmulCost' : square.2 ≤ 8 * (2 * W + 2) * (W + 1) := by
          simpa [square, two_mul, Nat.add_comm, Nat.add_left_comm,
            Nat.add_assoc] using hmulCost
        omega
      have hrest := ih hremWidth
      simp only [rawCandidateFrobeniusAuxBitCosted]
      calc
        _ ≤ rawRabinFrobeniusStepCharge W +
            d * rawRabinFrobeniusStepCharge W := by
              exact Nat.add_le_add hlocal hrest
        _ = (d + 1) * rawRabinFrobeniusStepCharge W := by
              rw [Nat.succ_mul]
              omega

end CorruptedFieldRecovery
