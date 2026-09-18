import Cryptography.Primitives

namespace Kriterion.Cryptography.BoundedMachine

/-- This budget covers the complete ArgoMAC arithmetic machine phase sum.
`compiledPhaseCost_polynomial` in `CompiledPhaseCost.lean` proves the local baseline bound. -/
def budget (queries : Nat) : Nat :=
  64 * queries ^ 2 + 2 ^ 27 * queries + 2 ^ 46

theorem budget_expanded (q : Nat) : budget q = 64 * q ^ 2 + 134217728 * q + 70368744177664 := by
  norm_num [budget]

/-- Each data word has 256 bits. Each register index has four bits. -/
abbrev Word := BitVec 256
abbrev Register := Fin 16

/-- These operations have fixed operands. The instruction set has no callbacks. -/
inductive Arithmetic
  | add | sub | mul | xor | and | shiftLeft | shiftRight | less
  | fieldAdd | fieldSub | fieldMul | fieldInv
  | scalarAdd | scalarSub | scalarMul | scalarInv
  deriving DecidableEq

def Arithmetic.eval (operation : Arithmetic) (left right : Word) : Word :=
  let base (x : Word) : BN254.BaseField := x.toNat
  let scalar (x : Word) : BN254.ScalarField := x.toNat
  match operation with
  | .add => left + right
  | .sub => left - right
  | .mul => left * right
  | .xor => left ^^^ right
  | .and => left &&& right
  | .shiftLeft => left <<< right.toNat
  | .shiftRight => left >>> right.toNat
  | .less => if left.toNat < right.toNat then 1 else 0
  | .fieldAdd => BitVec.ofNat 256 (base left + base right).val
  | .fieldSub => BitVec.ofNat 256 (base left - base right).val
  | .fieldMul => BitVec.ofNat 256 (base left * base right).val
  | .fieldInv => BitVec.ofNat 256 ((base left)⁻¹).val
  | .scalarAdd => BitVec.ofNat 256 (scalar left + scalar right).val
  | .scalarSub => BitVec.ofNat 256 (scalar left - scalar right).val
  | .scalarMul => BitVec.ofNat 256 (scalar left * scalar right).val
  | .scalarInv => BitVec.ofNat 256 ((scalar left)⁻¹).val

/-- A point uses one tag and two coordinates. Tag zero denotes the identity. -/
structure PointRegisters where
  tag : Register
  x : Register
  y : Register
  deriving DecidableEq

/-- The decoder rejects invalid tags and noncanonical coordinates. -/
def readPoint [BN254.FieldCertificate] (registers : Register → Word) (source : PointRegisters) :
    Option BN254.Point :=
  if registers source.tag = 0 then some 0
  else if registers source.tag = 1 ∧
      (registers source.x).toNat < BN254.baseFieldModulus ∧
      (registers source.y).toNat < BN254.baseFieldModulus then
    BN254.decodePoint ⟨(registers source.x).toNat, (registers source.y).toNat⟩
  else none

def writePoint [BN254.FieldCertificate] (registers : Register → Word) (target : PointRegisters)
    (point : BN254.Point) : Register → Word :=
  let values : Word × Word × Word := match point with
    | .zero => (0, 0, 0)
    | .some x y _ => (1, BitVec.ofNat 256 x.val, BitVec.ofNat 256 y.val)
  Function.update (Function.update (Function.update registers target.tag values.1)
    target.x values.2.1) target.y values.2.2

/-- Each instruction charges one unit. The machine has no external function calls. -/
inductive Instruction (labels : Nat)
  | halt
  | push (stack : Fin 4) (bit : Bool) (next : Fin labels)
  | pop (stack : Fin 4) (empty zero one : Fin labels)
  | coin (stack : Fin 4) (next : Fin labels)
  | constant (target : Register) (value : Word) (next : Fin labels)
  | arithmetic (operation : Arithmetic) (target left right : Register) (next : Fin labels)
  | load (target address : Register) (next : Fin labels)
  | store (address source : Register) (next : Fin labels)
  | branch (source : Register) (zero nonzero : Fin labels)
  | pushBit (stack : Fin 4) (source : Register) (next : Fin labels)
  | pointAdd (target left right : PointRegisters) (next : Fin labels)
  deriving DecidableEq

structure Machine where
  size : Nat
  code : Vector (Instruction (size + 1)) (size + 1)
  /-- The program counter has a fixed width. -/
  addressBound : size < 2 ^ 256 := by decide

structure Memory where
  bits : Fin 4 → List Bool := fun _ => []
  registers : Register → Word := fun _ => 0
  ram : Word → Word := fun _ => 0

structure Configuration (labels : Nat) where
  pc : Fin labels
  memory : Memory

/-- The flag distinguishes a halt from a continuation. Failure aborts the execution. -/
noncomputable def step [BN254.FieldCertificate] (machine : Machine)
    (state : Configuration (machine.size + 1)) :
    PMF (Option (Bool × Configuration (machine.size + 1))) :=
  let resume pc memory := PMF.pure (some (false, ⟨pc, memory⟩))
  let assign target value next := resume next
    { state.memory with registers := Function.update state.memory.registers target value }
  let push stack bit next := resume next
    { state.memory with bits := Function.update state.memory.bits stack (bit :: state.memory.bits stack) }
  let registers := state.memory.registers
  match machine.code[state.pc.val] with
  | .halt => PMF.pure (some (true, state))
  | .push stack bit next => push stack bit next
  | .pop stack empty zero one =>
      match state.memory.bits stack with
      | [] => resume empty state.memory
      | bit :: rest => resume (if bit then one else zero)
          { state.memory with bits := Function.update state.memory.bits stack rest }
  | .coin stack next => (PMF.uniformOfFintype Bool).bind fun bit => push stack bit next
  | .constant target value next => assign target value next
  | .arithmetic operation target left right next =>
      assign target (operation.eval (registers left) (registers right)) next
  | .load target address next => assign target (state.memory.ram (registers address)) next
  | .store address source next => resume next
      { state.memory with ram := Function.update state.memory.ram (registers address) (registers source) }
  | .branch source zero nonzero => resume (if registers source = 0 then zero else nonzero) state.memory
  | .pushBit stack source next => push stack ((registers source).getLsbD 0) next
  | .pointAdd target left right next =>
      match readPoint registers left, readPoint registers right with
      | some a, some b => resume next
          { state.memory with registers := writePoint registers target (a + b) }
      | _, _ => PMF.pure none

/-- The interpreter charges control flow, data access, random bits, and halts. -/
noncomputable def run [BN254.FieldCertificate] (machine : Machine) :
    Nat → Configuration (machine.size + 1) → PMF (Option (Configuration (machine.size + 1) × Nat))
  | 0, _ => PMF.pure none
  | fuel + 1, state => (step machine state).bind fun outcome =>
      match outcome with
      | none => PMF.pure none
      | some (true, next) => PMF.pure (some (next, 1))
      | some (false, next) => (run machine fuel next).map
          (Option.map fun result => (result.1, result.2 + 1))

/-- Every successful execution stays within its supplied fuel. -/
theorem run_cost [BN254.FieldCertificate] (machine : Machine) (fuel : Nat)
    (state result : Configuration (machine.size + 1)) (cost : Nat)
    (member : some (result, cost) ∈ (run machine fuel state).support) : cost ≤ fuel := by
  induction fuel generalizing state result cost with
  | zero => simp [run] at member
  | succ fuel ih =>
    simp only [run, PMF.mem_support_bind_iff] at member
    obtain ⟨outcome, _, member⟩ := member
    cases outcome with
    | none => simp at member
    | some outcome =>
      rcases outcome with ⟨halted, next⟩
      cases halted with
      | true => simp at member; omega
      | false =>
        rw [PMF.support_map] at member
        obtain ⟨value, supported, same⟩ := member
        cases value with
        | none => simp at same
        | some value =>
          cases same
          exact Nat.add_le_add_right (ih next value.1 value.2 supported) 1

/-- The shared counter includes setup, both stages, and every oracle response. -/
structure State where
  memory : Memory := {}
  spent : Nat
  queries : Nat := 0

/-- The machine pays for its control table before it receives any input. -/
def initial (machine : Machine) : State := ⟨{}, machine.size + 1, 0⟩

/-- Stack zero receives the request. Stack three returns the response.
The machine retains its registers, RAM, and stacks one and two across requests. -/
noncomputable def respond [BN254.FieldCertificate] (machine : Machine) (request : List Bool) (state : State) :
    PMF (Option (List Bool × State)) :=
  if state.spent ≤ budget state.queries then
    (run machine (budget state.queries - state.spent)
      ⟨0, { state.memory with bits := Function.update (Function.update state.memory.bits 0 request) 3 [] }⟩).map
      (Option.map fun result => (result.1.memory.bits 3,
        ⟨result.1.memory, state.spent + result.2, state.queries⟩))
  else PMF.pure none

/-- A response retains the accumulated charge. A new request cannot reset the budget. -/
theorem respond_cost [BN254.FieldCertificate] (machine : Machine) (request : List Bool) (state updated : State) (wire : List Bool)
    (member : some (wire, updated) ∈ (respond machine request state).support) :
    state.spent ≤ updated.spent ∧ updated.spent ≤ budget updated.queries := by
  unfold respond at member
  split at member
  · rename_i available
    rw [PMF.support_map] at member
    obtain ⟨result, supported, same⟩ := member
    cases result with
    | none => simp at same
    | some result =>
      cases same
      have bound := run_cost machine _ _ result.1 result.2 supported
      dsimp
      omega
  · simp at member

end Kriterion.Cryptography.BoundedMachine
