import Lean.Elab.Tactic.Omega

/-!
Partial M0 prototype: a one-bit, cost-instrumented ripple-adder machine.

The one-bit FSM below executes its represented read, Boolean-gate, write and
instruction-advance transitions.  It computes a peak over the named RAM state
at every transition.  This is deliberately scoped to one adder stage.  It
does not certify a variable-size finite-array implementation, initialization
costs for a word output buffer, address generation for a k-bit word, or the
runtime stack/list representation used by Lean's recursive interpreter.
Accordingly, it proves no O(k) implementation-space claim and no manuscript
recovery cost bound.
-/

namespace CorruptedFieldRecovery.BitCostPrototype

abbrev Word := List Bool

def bitVal (b : Bool) : Nat := if b then 1 else 0

def xorBit (a b : Bool) : Bool := decide (a ≠ b)

def andBit (a b : Bool) : Bool := a && b

def orBit (a b : Bool) : Bool := a || b

/-- The mathematical full-adder circuit used as the erasure target. -/
def fullAdder (x y carry : Bool) : Bool × Bool :=
  let p := xorBit x y
  let sum := xorBit p carry
  let carryOut := orBit (andBit x y) (andBit carry p)
  (sum, carryOut)

theorem fullAdder_correct (x y carry : Bool) :
    bitVal x + bitVal y + bitVal carry =
      bitVal (fullAdder x y carry).1 + 2 * bitVal (fullAdder x y carry).2 := by
  cases x <;> cases y <;> cases carry <;> decide

/-- A least-significant-bit-first integer interpretation. -/
def value : Word → Nat
  | [] => 0
  | b :: bs => bitVal b + 2 * value bs

/-- The primitive instructions of one represented full-adder stage. -/
inductive Op where
  | readX
  | readY
  | xorXY
  | xorCarry
  | andXY
  | andCarryP
  | orCarry
  | writeOutput
  deriving Repr, DecidableEq

/-- Each cost component counts charged bit operations. -/
structure Charge where
  reads : Nat := 0
  writes : Nat := 0
  gates : Nat := 0
  controlBits : Nat := 0
  deriving Repr, DecidableEq

def Charge.total (c : Charge) : Nat :=
  c.reads + c.writes + c.gates + c.controlBits

def Charge.add (a b : Charge) : Charge :=
  ⟨a.reads + b.reads, a.writes + b.writes, a.gates + b.gates,
    a.controlBits + b.controlBits⟩

def addressWidth (k : Nat) : Nat := Nat.log2 (k + 1) + 1

/-- Fixed one-bit FSM state. `programBits = 8 * 3` stores its eight 3-bit
opcodes. The four-bit PC can address the eight instructions and halt slot. -/
structure State where
  inputX : Bool := false
  inputY : Bool := false
  carryIn : Bool := false
  xReg : Bool := false
  yReg : Bool := false
  pReg : Bool := false
  sumReg : Bool := false
  xyReg : Bool := false
  carryPReg : Bool := false
  carryOutReg : Bool := false
  outputReg : Option Bool := none
  pc : Nat := 0
  /- `charge` is ghost accounting metadata, excluded from operational storage.
     The instrumented semantics records charges; it does not charge its own
     proof-monitor arithmetic. -/
  charge : Charge := {}
  deriving Repr, DecidableEq

def opcodeBits : Nat := 3
def programLength : Nat := 8
def programBits : Nat := opcodeBits * programLength
def pcBits : Nat := 4

/-- Live operational RAM bits for the declared one-bit state: inputs,
registers, output slot, PC and fixed 3-bit-opcode instruction storage. The
instrumentation counters are ghost data and are excluded. -/
def declaredLiveBits (_k : Nat) (_s : State) : Nat :=
  3 + 2 + 5 + 2 + pcBits + programBits

/-- The state models two already-selected input bits, statically named local
registers, and one output bit. Statically named register accesses use fixed
names and need no variable address bits. Each of the two input-array reads and
the output-array write charges `addressWidth k`; every instruction also
charges three opcode-fetch bits and four PC-update bits. The actual pc-indexed
fetch remains an explicit unproved interpreter obligation below. -/
def opCharge (k : Nat) (op : Op) : Charge :=
  let addr := addressWidth k
  let control (arrayAccesses : Nat) := arrayAccesses * addr + opcodeBits + pcBits
  match op with
  | .readX => ⟨1, 1, 0, control 1⟩
  | .readY => ⟨1, 1, 0, control 1⟩
  | .xorXY => ⟨2, 1, 1, control 0⟩
  | .xorCarry => ⟨2, 1, 1, control 0⟩
  | .andXY => ⟨2, 1, 1, control 0⟩
  | .andCarryP => ⟨2, 1, 1, control 0⟩
  | .orCarry => ⟨2, 1, 1, control 0⟩
  | .writeOutput => ⟨1, 1, 0, control 1⟩

/-- Execute one actual represented primitive and advance the instruction
counter. The output write allocates its output bit in the state. -/
def advance (k : Nat) (op : Op) (s : State) : State :=
  let changed := match op with
    | .readX => { s with xReg := s.inputX }
    | .readY => { s with yReg := s.inputY }
    | .xorXY => { s with pReg := xorBit s.xReg s.yReg }
    | .xorCarry => { s with sumReg := xorBit s.pReg s.carryIn }
    | .andXY => { s with xyReg := andBit s.xReg s.yReg }
    | .andCarryP => { s with carryPReg := andBit s.carryIn s.pReg }
    | .orCarry => { s with carryOutReg := orBit s.xyReg s.carryPReg }
    | .writeOutput => { s with outputReg := some s.sumReg }
  { changed with
    pc := s.pc + 1
    charge := Charge.add s.charge (opCharge k op) }

def program : List Op :=
  [.readX, .readY, .xorXY, .xorCarry, .andXY, .andCarryP, .orCarry, .writeOutput]

structure RunReport where
  final : State
  peakDeclaredBits : Nat
  deriving Repr, DecidableEq

/-- Execute the listed instructions one by one; the reported peak is the max
of the declared live-bit measure before and after every represented action. -/
def execute (k : Nat) : List Op → State → RunReport
  | [], s => ⟨s, declaredLiveBits k s⟩
  | op :: ops, s =>
      let s' := advance k op s
      let rest := execute k ops s'
      ⟨rest.final, max (declaredLiveBits k s) rest.peakDeclaredBits⟩
termination_by ops s => ops.length
decreasing_by all_goals simp_wf

def initialState (x y carry : Bool) : State :=
  { inputX := x, inputY := y, carryIn := carry }

def stage (k : Nat) (x y carry : Bool) : RunReport :=
  execute k program (initialState x y carry)

def erasure (s : State) : Bool × Bool :=
  (s.outputReg.getD false, s.carryOutReg)

theorem stage_erasure (k : Nat) (x y carry : Bool) :
    erasure (stage k x y carry).final = fullAdder x y carry := by
  cases x <;> cases y <;> cases carry <;> rfl

theorem stage_charge (k : Nat) (x y carry : Bool) :
    (stage k x y carry).final.charge.reads = 13 ∧
    (stage k x y carry).final.charge.writes = 8 ∧
    (stage k x y carry).final.charge.gates = 5 ∧
    (stage k x y carry).final.charge.controlBits =
      3 * addressWidth k + 8 * (opcodeBits + pcBits) := by
  simp [stage, execute, program, initialState, advance, opCharge,
    Charge.add, addressWidth, opcodeBits, pcBits]

/-- Exact total charged operations for one executed stage. -/
theorem stage_total_charge (k : Nat) (x y carry : Bool) :
    (stage k x y carry).final.charge.total =
      82 + 3 * addressWidth k := by
  have h := stage_charge k x y carry
  rcases h with ⟨hr, hw, hg, hc⟩
  simp [Charge.total, hr, hw, hg, hc]

/-- The cost-model's declared measure is the constant 40 for every state.
This is only an equation for the selected measure: `pc` is represented by an
unbounded `Nat`, and this theorem does not prove that four bits suffice for
arbitrary states/operation lists or that the measure captures runtime memory. -/
theorem execute_declared_measure_exact (k : Nat) (ops : List Op) (s : State) :
    (execute k ops s).peakDeclaredBits = 40 := by
  induction ops generalizing s with
  | nil => simp [execute, declaredLiveBits, pcBits, programBits, opcodeBits]
  | cons op ops ih =>
      simp [execute, declaredLiveBits, pcBits, programBits, opcodeBits, ih]

/-- The executed stage reports 40 under the declared cost-model measure only;
this is not a proof of actual peak storage or of PC-layout adequacy. -/
theorem stage_declared_measure_exact (k : Nat) (x y carry : Bool) :
    (stage k x y carry).peakDeclaredBits = 40 := by
  simp [stage, execute_declared_measure_exact]

/-- The full-word arithmetic program, stated independently of a RAM scaling
claim. Each call executes the one-bit FSM and erases its final registers. -/
def ripple : Word → Word → Bool → Word × Bool
  | [], [], carry => ([], carry)
  | x :: xs, y :: ys, carry =>
      let one := erasure (stage (xs.length + 1) x y carry).final
      let rest := ripple xs ys one.2
      (one.1 :: rest.1, rest.2)
  | _, _, carry => ([], carry)
termination_by xs ys carry => xs.length
decreasing_by all_goals simp_wf

theorem ripple_correct (xs ys : Word) (carry : Bool)
    (hLen : xs.length = ys.length) :
    value xs + value ys + bitVal carry =
      value (ripple xs ys carry).1 +
        2 ^ xs.length * bitVal (ripple xs ys carry).2 := by
  induction xs generalizing ys carry with
  | nil =>
      cases ys with
      | nil => simp [ripple, value]
      | cons y ys => simp at hLen
  | cons x xs ih =>
      cases ys with
      | nil => simp at hLen
      | cons y ys =>
          have hTail : xs.length = ys.length := by simpa using hLen
          have hGate := fullAdder_correct x y carry
          have hRest := ih ys (fullAdder x y carry).2 hTail
          simp only [ripple, stage_erasure, value]
          dsimp [fullAdder] at hGate hRest ⊢
          simp only [List.length_cons, pow_succ]
          omega

/-! ### Scope and unresolved refinements

The FSM and `stage_charge` account for each one-bit input/register read and
write, Boolean gate, the two input-array and one output-array address widths,
opcode-fetch bits and PC-update bits in the declared cost model. Local
registers are statically named. `stage_declared_measure_exact` proves only
that the selected measure evaluates to 40; it does not prove actual peak
storage or four-bit PC adequacy. Charge counters are ghost instrumentation,
not runtime memory, and their update cost is not included. The source-level execution uses
Lean records, a finite instruction list and structural recursion. In
particular, `execute` consumes the next `Op` from a Lean list rather than
fetching/checking an opcode from a represented instruction store by `pc`; its
fetch and PC charges are a conservative modeled accounting, not a proved
pc-indexed interpreter. Refinement of those objects and the recursion stack
to the named RAM measure is not proved. Extending the FSM to k-bit mutable
arrays, charging output initialization, proving the scaled peak-storage
bound, and showing the complete word program's interpreter overhead are open
M0 work. No manuscript recovery complexity or implementation-space theorem
follows.
-/

end CorruptedFieldRecovery.BitCostPrototype
