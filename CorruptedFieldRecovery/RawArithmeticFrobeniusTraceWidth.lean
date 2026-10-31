import CorruptedFieldRecovery.RawArithmeticGcdTraceWidth
import CorruptedFieldRecovery.RawArithmeticFrameBounds

/-! Reachable repeated-square Frobenius snapshots for the costed Nat-mask
evaluator. The register theorem includes the intermediate square, so it uses
a 2W-bit arithmetic envelope. It is an explicit abstract register invariant,
not a claim about Lean's evaluator stack or heap. -/

namespace CorruptedFieldRecovery

private theorem rawFrobenius_lt_parameter_of_lt_pow
    {n v W : Nat} (hn : n < 2 ^ v) (hv : v ≤ W) :
    n < 2 ^ rawArithmeticParameterWidth W := by
  exact lt_of_lt_of_le hn
    (Nat.pow_le_pow_right (by decide : 0 < 2) (by
      unfold rawArithmeticParameterWidth
      omega))

private theorem rawFrobenius_le_parameter
    {n W : Nat} (hn : n ≤ W) :
    n < 2 ^ rawArithmeticParameterWidth W := by
  have hlog : W + 1 < 2 ^ (Nat.log2 (W + 1) + 1) := Nat.lt_log2_self
  have hexp : Nat.log2 (W + 1) + 1 ≤ rawArithmeticParameterWidth W := by
    unfold rawArithmeticParameterWidth
    omega
  have hpow : 2 ^ (Nat.log2 (W + 1) + 1) ≤
      2 ^ rawArithmeticParameterWidth W :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hexp
  omega

/-- Activation snapshots along the exact repeated quotient-square recursion.
Each frame records the modulus, remaining iteration count, current mask,
square, and reduced remainder. -/
def rawCandidateFrobeniusActivationTrace (modulus : Nat) :
    Nat → Nat → List RawArithmeticFrame
  | 0, x => [rawArithmeticFrobeniusFrame modulus 0 x x 0]
  | d + 1, x =>
      let square := rawPolyMulBitCosted x x
      let rem := rawPolynomialRemainderBitCosted square.1 modulus
      rawArithmeticFrobeniusFrame modulus (d + 1) x square.1 rem.1 ::
        rawCandidateFrobeniusActivationTrace modulus d rem.1
termination_by d _ => d
decreasing_by omega

/-- Every listed register on a Frobenius activation path fits a parameterized
2W-bit envelope. The square is the largest value in one such snapshot. -/
theorem rawCandidateFrobeniusActivationTrace_registers_lt
    {modulus d x W : Nat} (hmod : modulus ≠ 0)
    (hmodWidth : modulus < 2 ^ W) (hW : 0 < W) (hd : d ≤ W)
    (hx : x < 2 ^ W) :
    ∀ frame ∈ rawCandidateFrobeniusActivationTrace modulus d x,
      ∀ word ∈ frame.registers,
        word < 2 ^ rawArithmeticParameterWidth (2 * W) := by
  have hWle : W ≤ 2 * W := by omega
  have hwordWidth {n : Nat} (hn : n < 2 ^ W) :
      n < 2 ^ rawArithmeticParameterWidth (2 * W) :=
    rawFrobenius_lt_parameter_of_lt_pow hn (by omega)
  have hcontrol {n : Nat} (hn : n ≤ 2 * W) :
      n < 2 ^ rawArithmeticParameterWidth (2 * W) :=
    rawFrobenius_le_parameter hn
  induction d generalizing x with
  | zero =>
      intro frame hframe word hword
      simp only [rawCandidateFrobeniusActivationTrace, List.mem_singleton] at hframe
      subst frame
      simp only [rawArithmeticFrobeniusFrame, List.mem_cons] at hword
      rcases hword with hmodulus | hdegree | hcurrent | hsquare | hrem
      · rw [hmodulus]
        exact hwordWidth hmodWidth
      · rw [hdegree]
        exact hcontrol (by omega)
      · rw [hcurrent]
        exact hwordWidth hx
      · rw [hsquare]
        exact hwordWidth hx
      · rcases hrem with hzero | hfalse
        · rw [hzero]
          exact Nat.pow_pos (by decide : 0 < (2 : Nat))
        · simp at hfalse
  | succ d ih =>
      have hdChild : d ≤ W := by omega
      let square := rawPolyMulBitCosted x x
      let rem := rawPolynomialRemainderBitCosted square.1 modulus
      have hSquareWidth : square.1 < 2 ^ (W + W) := by
        rw [show square.1 = rawPolyMul x x by
          dsimp [square]
          exact rawPolyMulBitCosted_fst x x]
        exact rawPolyMul_lt_pow W W x x hx hx
      have hrem : rem.1 < 2 ^ W := by
        rw [show rem.1 = rawPolynomialRemainder square.1 modulus by
          dsimp [rem]
          exact rawPolynomialRemainderBitCosted_fst square.1 modulus]
        exact lt_trans (rawPolynomialRemainder_lt hmod) hmodWidth
      have hparent : ∀ word ∈
          (rawArithmeticFrobeniusFrame modulus (d + 1) x square.1 rem.1).registers,
          word < 2 ^ rawArithmeticParameterWidth (2 * W) := by
        intro word hword
        simp only [rawArithmeticFrobeniusFrame, List.mem_cons] at hword
        rcases hword with hmodulus | hdegree | hcurrent | hsquareEq | hremEq
        · rw [hmodulus]
          exact hwordWidth hmodWidth
        · rw [hdegree]
          exact hcontrol (by omega)
        · rw [hcurrent]
          exact hwordWidth hx
        · rw [hsquareEq]
          exact rawFrobenius_lt_parameter_of_lt_pow hSquareWidth (by omega)
        · rcases hremEq with hremEq | hfalse
          · rw [hremEq]
            exact hwordWidth hrem
          · simp at hfalse
      intro frame hframes word hword
      simp only [rawCandidateFrobeniusActivationTrace, List.mem_cons] at hframes
      rcases hframes with hhead | htail
      · subst frame
        exact hparent word hword
      · exact ih hdChild hrem frame htail word hword

/-- Trace length is bounded by the exact recursive frame count, then by the
accepted declared Frobenius charge plus the base activation. -/
theorem rawCandidateFrobeniusActivationTrace_length_le_charge
    (modulus d x : Nat) :
    (rawCandidateFrobeniusActivationTrace modulus d x).length ≤
      (rawCandidateFrobeniusAuxBitCosted modulus d x).2 + 1 := by
  have hframes : ∀ k y,
      (rawCandidateFrobeniusActivationTrace modulus k y).length ≤
        rawCandidateFrobeniusAuxBitCostedFrames modulus k y := by
    intro k
    induction k with
    | zero => intro y; simp [rawCandidateFrobeniusActivationTrace,
        rawCandidateFrobeniusAuxBitCostedFrames]
    | succ k ih =>
        intro y
        let square := rawPolyMulBitCosted y y
        let rem := rawPolynomialRemainderBitCosted square.1 modulus
        simp only [rawCandidateFrobeniusActivationTrace, List.length_cons,
          rawCandidateFrobeniusAuxBitCostedFrames]
        have hchild := ih rem.1
        dsimp [square, rem] at hchild
        omega
  exact le_trans (hframes d x)
    (rawCandidateFrobeniusAuxBitCostedFrames_le_charge_add_one modulus d x)

end CorruptedFieldRecovery
