import CorruptedFieldRecovery.RawArithmeticFrameBounds

/-! Explicit register snapshots for the recursive arithmetic space model.
These structures model the operands and saved intermediates in one activation
frame. Their bit bounds are conditional on a proved width invariant for every
stored Nat; this is not a claim about Lean's runtime heap. -/

namespace CorruptedFieldRecovery

/-- The arithmetic operation whose activation is represented by a frame. -/
inductive RawArithmeticFrameKind
  | multiply
  | reduce
  | gcd
  | frobenius
  deriving DecidableEq, Repr

/-- One explicit activation snapshot. `registers` lists Nat operands and any
intermediate values retained across a recursive child. The tag costs two
control bits in this abstract model. -/
structure RawArithmeticFrame where
  kind : RawArithmeticFrameKind
  registers : List Nat
  register_count_le : registers.length ≤ 6

/-- Snapshot of the multiplier locals live while a recursive child runs or
returns. -/
def rawArithmeticMultiplyFrame (a b child shifted : Nat) : RawArithmeticFrame :=
  ⟨.multiply, [a, b, child, shifted], by simp⟩

/-- Snapshot of the reduction locals: modulus, degree, remaining fuel, current
representative, shifted modulus, and XOR result. -/
def rawArithmeticReduceFrame
    (modulus degree fuel current shifted output : Nat) : RawArithmeticFrame :=
  ⟨.reduce, [modulus, degree, fuel, current, shifted, output], by simp⟩

/-- Snapshot of one Euclidean recursion level and its saved remainder/result. -/
def rawArithmeticGcdFrame (a b remainder child : Nat) : RawArithmeticFrame :=
  ⟨.gcd, [a, b, remainder, child], by simp⟩

/-- Snapshot of a repeated-squaring iteration and its saved square/remainder. -/
def rawArithmeticFrobeniusFrame
    (modulus degree current square remainder : Nat) : RawArithmeticFrame :=
  ⟨.frobenius, [modulus, degree, current, square, remainder], by simp⟩

/-- A stack of arithmetic activations, ordered from caller to current frame. -/
abbrev RawArithmeticStack := List RawArithmeticFrame

/-- Number of live bits assigned to one frame: three control bits plus the
width of every Nat register, charging zero as one bit. -/
def rawArithmeticFrameLiveBits (frame : RawArithmeticFrame) : Nat :=
  3 + frame.registers.foldl (fun total word => total + rawNatBitWidth word) 0

/-- Live bits in the explicit arithmetic activation stack. -/
def rawArithmeticStackLiveBits (stack : RawArithmeticStack) : Nat :=
  stack.foldl (fun total frame => total + rawArithmeticFrameLiveBits frame) 0

private theorem rawNatBitWidth_le_of_lt_pow {n W : Nat}
    (hn : n < 2 ^ W) : rawNatBitWidth n ≤ W + 1 := by
  by_cases hn0 : n = 0
  · simp [rawNatBitWidth, hn0]
  · have hW : 0 < W := by
      cases W with
      | zero => simp at hn; omega
      | succ W => omega
    have hlog := rawLog2_lt_of_lt_pow hW hn
    unfold rawNatBitWidth
    omega

private theorem rawArithmeticRegisterWidthSum_le
    (registers : List Nat) (W acc : Nat)
    (hwidth : ∀ word ∈ registers, word < 2 ^ W) :
    registers.foldl (fun total word => total + rawNatBitWidth word) acc ≤
      acc + registers.length * (W + 1) := by
  induction registers generalizing acc with
  | nil => simp
  | cons word tail ih =>
      simp only [List.foldl_cons, List.length_cons]
      have hword := rawNatBitWidth_le_of_lt_pow (hwidth word (by simp))
      have htailWidth : ∀ x ∈ tail, x < 2 ^ W := by
        intro x hx
        exact hwidth x (by simp [hx])
      have htail := ih (acc + rawNatBitWidth word) htailWidth
      calc
        _ ≤ acc + rawNatBitWidth word + tail.length * (W + 1) := htail
        _ ≤ acc + (tail.length + 1) * (W + 1) := by
          rw [Nat.add_mul]
          omega

/-- If every saved Nat register has at most W bits, one activation frame uses
at most `3 + 6*(W+1)` live bits in this explicit register model. -/
theorem rawArithmeticFrameLiveBits_le
    (frame : RawArithmeticFrame) (W : Nat)
    (hwidth : ∀ word ∈ frame.registers, word < 2 ^ W) :
    rawArithmeticFrameLiveBits frame ≤ 3 + 6 * (W + 1) := by
  unfold rawArithmeticFrameLiveBits
  have h := rawArithmeticRegisterWidthSum_le frame.registers W 0 hwidth
  have hcount := frame.register_count_le
  have hmul := Nat.mul_le_mul_right (W + 1) hcount
  omega

private theorem rawArithmeticFrameSum_le
    (stack : RawArithmeticStack) (B acc : Nat)
    (hframe : ∀ frame ∈ stack, rawArithmeticFrameLiveBits frame ≤ B) :
    stack.foldl (fun total frame => total + rawArithmeticFrameLiveBits frame) acc ≤
      acc + stack.length * B := by
  induction stack generalizing acc with
  | nil => simp
  | cons frame tail ih =>
      simp only [List.foldl_cons, List.length_cons]
      have hhead := hframe frame (by simp)
      have htailBound : ∀ f ∈ tail, rawArithmeticFrameLiveBits f ≤ B := by
        intro f hf
        exact hframe f (by simp [hf])
      have htail := ih (acc + rawArithmeticFrameLiveBits frame) htailBound
      calc
        _ ≤ acc + rawArithmeticFrameLiveBits frame + tail.length * B := htail
        _ ≤ acc + (tail.length + 1) * B := by
          rw [Nat.add_mul]
          omega

/-- A stack of `F` frames with W-bit Nat registers has an explicit live-bit
bound linear in F and W. -/
theorem rawArithmeticStackLiveBits_le
    (stack : RawArithmeticStack) (F W : Nat)
    (hframes : stack.length ≤ F)
    (hwidth : ∀ frame ∈ stack, ∀ word ∈ frame.registers, word < 2 ^ W) :
    rawArithmeticStackLiveBits stack ≤ F * (3 + 6 * (W + 1)) := by
  have hframeBound : ∀ frame ∈ stack,
      rawArithmeticFrameLiveBits frame ≤ 3 + 6 * (W + 1) := by
    intro frame hf
    exact rawArithmeticFrameLiveBits_le frame W (hwidth frame hf)
  have hsum := rawArithmeticFrameSum_le stack (3 + 6 * (W + 1)) 0 hframeBound
  unfold rawArithmeticStackLiveBits at hsum ⊢
  nlinarith

/-- Connect a concrete frame-count bound to the generic register-space model.
Callers supply the explicit saved-register stack and prove its width invariant. -/
theorem rawArithmeticStackLiveBits_le_of_charge
    (stack : RawArithmeticStack) (charge W offset : Nat)
    (hframes : stack.length ≤ charge + offset)
    (hwidth : ∀ frame ∈ stack, ∀ word ∈ frame.registers, word < 2 ^ W) :
    rawArithmeticStackLiveBits stack ≤
      (charge + offset) * (3 + 6 * (W + 1)) :=
  rawArithmeticStackLiveBits_le stack (charge + offset) W hframes hwidth

end CorruptedFieldRecovery
