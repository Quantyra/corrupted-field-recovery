import CorruptedFieldRecovery.RawCandidateVerifierSpaceModel
import CorruptedFieldRecovery.RawRabinGcdBitCost
import CorruptedFieldRecovery.RawRabinFrobeniusBitCost
import CorruptedFieldRecovery.RawReductionBitCost

/-! Call-stack bounds for the actual recursive arithmetic evaluators. Each
frame count follows the same recursive call as its costed counterpart; local
bit charges dominate the number of simultaneously active frames. -/

namespace CorruptedFieldRecovery

/-- Recursive call-frame count for the costed carryless multiplier. -/
def rawPolyMulBitCostedFrames : Nat → Nat
  | 0 => 1
  | b + 1 => 1 + rawPolyMulBitCostedFrames ((b + 1) / 2)
termination_by b => b
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

theorem rawPolyMulBitCostedFrames_le_charge (a b : Nat) :
    rawPolyMulBitCostedFrames b ≤ (rawPolyMulBitCosted a b).2 := by
  induction b using Nat.strong_induction_on with
  | h b ih =>
      cases b with
      | zero => simp [rawPolyMulBitCostedFrames, rawPolyMulBitCosted, rawNatBitWidth]
      | succ b =>
          have hdiv : (b + 1) / 2 < b + 1 := Nat.div_lt_self (by omega) (by decide)
          have hchild := ih ((b + 1) / 2) hdiv
          simp only [rawPolyMulBitCostedFrames, rawPolyMulBitCosted]
          omega

/-- Frame count for a costed Euclidean call; the recursive child is precisely
the remainder call made by `rawPolynomialGcdBitCosted`. -/
def rawPolynomialGcdBitCostedFrames : Nat → Nat → Nat
  | _, 0 => 1
  | _, 1 => 1
  | a, b + 2 =>
      let rem := rawPolynomialRemainderBitCosted a (b + 2)
      1 + rawPolynomialGcdBitCostedFrames (b + 2) rem.1
termination_by _ b => b
decreasing_by
  rw [rawPolynomialRemainderBitCosted_fst]
  exact rawPolynomialRemainder_lt (by omega)

theorem rawPolynomialGcdBitCostedFrames_le_charge (a b : Nat) :
    rawPolynomialGcdBitCostedFrames a b ≤ (rawPolynomialGcdBitCosted a b).2 := by
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
      cases b with
      | zero => simp [rawPolynomialGcdBitCostedFrames, rawPolynomialGcdBitCosted,
          rawNatBitWidth]
      | succ b =>
          cases b with
          | zero => simp [rawPolynomialGcdBitCostedFrames,
              rawPolynomialGcdBitCosted, rawNatBitWidth]
          | succ b =>
              let rem := rawPolynomialRemainderBitCosted a (b + 2)
              have hrem : rem.1 < b + 2 := by
                rw [rawPolynomialRemainderBitCosted_fst]
                exact rawPolynomialRemainder_lt (by omega)
              have hchild := ih rem.1 hrem (b + 2)
              dsimp [rem] at hchild
              simp only [rawPolynomialGcdBitCostedFrames, rawPolynomialGcdBitCosted]
              have hwidth : 1 ≤ rawNatBitWidth (b + 2) := by
                unfold rawNatBitWidth
                omega
              omega

/-- Frame count for the bounded cancellation loop. This follows the actual
stop condition, so a successful early stop does not count skipped frames. -/
def rawReduceFuelBitCostedFrames (modulus degree : Nat) : Nat → Nat → Nat
  | 0, _ => 1
  | fuel + 1, a =>
      if a < 2 ^ degree then 1
      else 1 + rawReduceFuelBitCostedFrames modulus degree fuel
        (rawReduceStepBitCosted modulus degree a).1

theorem rawReduceFuelBitCostedFrames_le_charge_add_one
    (modulus degree fuel a : Nat) :
    rawReduceFuelBitCostedFrames modulus degree fuel a ≤
      (rawReduceFuelBitCosted modulus degree fuel a).2 + 1 := by
  induction fuel generalizing a with
  | zero => simp [rawReduceFuelBitCostedFrames, rawReduceFuelBitCosted]
  | succ fuel ih =>
      by_cases hsmall : a < 2 ^ degree
      · simp [rawReduceFuelBitCostedFrames, rawReduceFuelBitCosted, hsmall]
      · have hstep := ih (rawReduceStepBitCosted modulus degree a).1
        simp only [rawReduceFuelBitCostedFrames, rawReduceFuelBitCosted, if_neg hsmall]
        omega

/-- Recursive frame count for the costed repeated-Frobenius evaluator. -/
def rawCandidateFrobeniusAuxBitCostedFrames : Nat → Nat → Nat → Nat
  | _, 0, _ => 1
  | modulus, d + 1, x =>
      let square := rawPolyMulBitCosted x x
      let rem := rawPolynomialRemainderBitCosted square.1 modulus
      1 + rawCandidateFrobeniusAuxBitCostedFrames modulus d rem.1
termination_by _ d _ => d
decreasing_by omega

theorem rawCandidateFrobeniusAuxBitCostedFrames_le_charge_add_one
    (modulus d x : Nat) :
    rawCandidateFrobeniusAuxBitCostedFrames modulus d x ≤
      (rawCandidateFrobeniusAuxBitCosted modulus d x).2 + 1 := by
  induction d generalizing x with
  | zero => simp [rawCandidateFrobeniusAuxBitCostedFrames,
      rawCandidateFrobeniusAuxBitCosted]
  | succ d ih =>
      let square := rawPolyMulBitCosted x x
      let rem := rawPolynomialRemainderBitCosted square.1 modulus
      have hchild := ih rem.1
      dsimp [square, rem] at hchild
      have hwidth : 1 ≤ rawNatBitWidth modulus := by
        unfold rawNatBitWidth
        omega
      simp only [rawCandidateFrobeniusAuxBitCostedFrames,
        rawCandidateFrobeniusAuxBitCosted]
      omega

end CorruptedFieldRecovery
