import CorruptedFieldRecovery.RawArithmeticFrobeniusTraceWidth
import CorruptedFieldRecovery.RawArithmeticRegisterSpaceModel

/-! Explicit live-bit bounds for the reachable GCD and repeated-Frobenius
activation traces. These statements concern the declared register-stack model;
they do not refine Lean's evaluator heap or machine execution. -/

namespace CorruptedFieldRecovery

/-- Under the accepted W-bit input hypotheses, the GCD activation trace's
explicit register-stack live-bit measure is bounded by its declared charge
times the parameterized per-frame envelope. -/
theorem rawPolynomialGcdActivationTrace_live_bits_le
    {a b W : Nat} (hW : 0 < W) (ha : a < 2 ^ W) (hb : b < 2 ^ W) :
    rawArithmeticStackLiveBits (rawPolynomialGcdActivationTrace a b) ≤
      (rawPolynomialGcdBitCosted a b).2 *
        (3 + 6 * (rawArithmeticParameterWidth W + 1)) := by
  apply rawArithmeticStackLiveBits_le
    (stack := rawPolynomialGcdActivationTrace a b)
    (F := (rawPolynomialGcdBitCosted a b).2)
    (W := rawArithmeticParameterWidth W)
  · exact rawPolynomialGcdActivationTrace_length_le_charge a b
  · intro frame hframe word hword
    exact rawPolynomialGcdActivationTrace_registers_lt hW ha hb frame hframe word hword

/-- The repeated-square activation trace uses at most `d+1` frames, including
the base activation. -/
theorem rawCandidateFrobeniusActivationTrace_length_le_iterations
    (modulus d x : Nat) :
    (rawCandidateFrobeniusActivationTrace modulus d x).length ≤ d + 1 := by
  induction d generalizing x with
  | zero => simp [rawCandidateFrobeniusActivationTrace]
  | succ d ih =>
      let square := rawPolyMulBitCosted x x
      let rem := rawPolynomialRemainderBitCosted square.1 modulus
      simp only [rawCandidateFrobeniusActivationTrace, List.length_cons]
      have hchild := ih rem.1
      dsimp [square, rem] at hchild
      omega

/-- Under a W-bit modulus/current representative and `d ≤ W`, the abstract
Frobenius activation stack's live-bit measure is at most its exact declared
charge plus the base activation, times the proved per-frame width envelope. -/
theorem rawCandidateFrobeniusActivationTrace_live_bits_le_charge
    {modulus d x W : Nat} (hmod : modulus ≠ 0)
    (hmodWidth : modulus < 2 ^ W) (hW : 0 < W) (hd : d ≤ W)
    (hx : x < 2 ^ W) :
    rawArithmeticStackLiveBits
        (rawCandidateFrobeniusActivationTrace modulus d x) ≤
      ((rawCandidateFrobeniusAuxBitCosted modulus d x).2 + 1) *
        (3 + 6 * (rawArithmeticParameterWidth (2 * W) + 1)) := by
  apply rawArithmeticStackLiveBits_le
    (stack := rawCandidateFrobeniusActivationTrace modulus d x)
    (F := (rawCandidateFrobeniusAuxBitCosted modulus d x).2 + 1)
    (W := rawArithmeticParameterWidth (2 * W))
  · exact rawCandidateFrobeniusActivationTrace_length_le_charge modulus d x
  · intro frame hframe word hword
    exact rawCandidateFrobeniusActivationTrace_registers_lt
      hmod hmodWidth hW hd hx frame hframe word hword

end CorruptedFieldRecovery
