import Cryptography.LazyOracle

namespace Kriterion.Cryptography.BoundedMachine

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

/-- Each oracle instruction has fixed register operands. The machine has no callbacks. -/
inductive OracleInstruction (labels : Nat)
  | compute (instruction : Instruction labels)
  | query (kind : Fin 5) (index input first second : Register) (next : Fin labels)
  deriving DecidableEq

/-- The two fuel bounds cover both adversary stages. The code charge prevents free advice. -/
structure Adversary where
  size : Nat
  code : Vector (OracleInstruction (size + 1)) (size + 1)
  addressBound : size < 2 ^ 256
  firstFuel : Nat
  secondFuel : Nat

def Adversary.steps (machine : Adversary) : Nat :=
  machine.size + 1 + machine.firstFuel + machine.secondFuel

def Adversary.arithmetic (machine : Adversary) : Machine :=
  ⟨machine.size, machine.code.map (fun instruction => match instruction with
    | .compute operation => operation | .query .. => .halt), machine.addressBound⟩

noncomputable def queryFromRegisters {FixedIndex EncIndex : Type}
    [Fintype FixedIndex] [Fintype EncIndex] (kind : Fin 5) (index input : Word) :
    Option (PublicQuery FixedIndex EncIndex) := by
  classical
  let fixed := if h : index.toNat < Fintype.card FixedIndex then
    some ((Fintype.equivFin FixedIndex).symm ⟨index.toNat, h⟩) else none
  let enc := if h : index.toNat < Fintype.card EncIndex then
    some ((Fintype.equivFin EncIndex).symm ⟨index.toNat, h⟩) else none
  let block := BitVec.ofNat 128 input.toNat
  exact match kind.val with
    | 0 => fixed.map (fun i => .fixedForward i block)
    | 1 => fixed.map (fun i => .fixedInverse i block)
    | 2 => enc.map (fun i => .encForward i block)
    | 3 => enc.map (fun i => .encInverse i block)
    | _ => some (.hash (input.toNat : BN254.BaseField))

def answerWords {FixedIndex EncIndex : Type} (query : PublicQuery FixedIndex EncIndex) :
    query.Answer → Word × Word :=
  match query with
  | .fixedForward .. | .fixedInverse .. | .encForward .. | .encInverse .. =>
      fun value => (BitVec.ofNat 256 value.toNat, 0)
  | .hash _ => fun value => (BitVec.ofNat 256 value.1.toNat, BitVec.ofNat 256 value.2.toNat)

/-- The translation charges each arithmetic, sampling, and query instruction against fuel. -/
noncomputable def Adversary.program [BN254.FieldCertificate] {FixedIndex EncIndex : Type}
    [Fintype FixedIndex] [Fintype EncIndex] (machine : Adversary) :
    (fuel : Nat) → Configuration (machine.size + 1) →
      OracleProgram (publicOracleSpec FixedIndex EncIndex)
        (Option (Configuration (machine.size + 1))) fuel
  | 0, _ => .pure (PMF.pure none)
  | fuel + 1, state => match machine.code[state.pc.val] with
    | .compute _ => .sample (step machine.arithmetic state) fun result => match result with
      | none => .pure (PMF.pure none)
      | some (true, stopped) => .pure (PMF.pure (some stopped))
      | some (false, next) => (machine.program fuel next).weaken
    | .query kind index input first second next =>
      match queryFromRegisters kind (state.memory.registers index) (state.memory.registers input) with
      | none => .pure (PMF.pure none)
      | some request => .query request fun answer =>
          let values := answerWords request answer
          let registers := Function.update (Function.update state.memory.registers first values.1) second values.2
          machine.program fuel ⟨next, { state.memory with registers }⟩

/-- The simulator alone can inspect and program the fixed oracle. -/
inductive SimulatorInstruction (labels : Nat)
  | compute (instruction : Instruction labels)
  | query (kind : Fin 5) (index input first second : Register) (next : Fin labels)
  | lookup (kind : Fin 5) (index input first second present : Register) (next : Fin labels)
  | program (kind : Fin 5) (index input first second : Register) (next : Fin labels)
  deriving DecidableEq

/-- One code table and two fuel bounds share the constant simulator allowance. -/
structure Simulator where
  size : Nat
  code : Vector (SimulatorInstruction (size + 1)) (size + 1)
  addressBound : size < 2 ^ 256
  firstFuel : Nat
  secondFuel : Nat
  within : size + 1 + firstFuel + secondFuel ≤ 2 ^ 60

abbrev Simulator.arithmetic (machine : Simulator) : Machine :=
  ⟨machine.size, machine.code.map (fun instruction => match instruction with
    | .compute operation => operation | _ => .halt), machine.addressBound⟩

/-- An arithmetic-only program uses the same closed instruction semantics. -/
abbrev Simulator.ofMachine (machine : Machine) (firstFuel secondFuel : Nat)
    (within : machine.size + 1 + firstFuel + secondFuel ≤ 2 ^ 60) : Simulator :=
  ⟨machine.size, machine.code.map SimulatorInstruction.compute, machine.addressBound,
    firstFuel, secondFuel, within⟩

@[simp] theorem Simulator.ofMachine_arithmetic (machine : Machine) (firstFuel secondFuel : Nat)
    (within : machine.size + 1 + firstFuel + secondFuel ≤ 2 ^ 60) :
    (Simulator.ofMachine machine firstFuel secondFuel within).arithmetic = machine := by
  cases machine
  simp [ofMachine, arithmetic, Vector.map_map, Function.comp_def]

def answerFromWords {FixedIndex EncIndex : Type} (query : PublicQuery FixedIndex EncIndex)
    (first second : Word) : query.Answer :=
  match query with
  | .fixedForward .. | .fixedInverse .. | .encForward .. | .encInverse .. =>
      BitVec.ofNat 128 first.toNat
  | .hash _ => (BitVec.ofNat 128 first.toNat, BitVec.ofNat 128 second.toNat)

/-- Every simulator oracle operation uses fixed register operands. -/
noncomputable def Simulator.step [BN254.FieldCertificate]
    {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex]
    [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (machine : Simulator) (state : Configuration (machine.size + 1))
    (oracle : LazyOracle.State FixedIndex EncIndex) :
    PMF (Option (Bool × Configuration (machine.size + 1) × LazyOracle.State FixedIndex EncIndex)) :=
  let resume next registers updated := some (false, (⟨next, { state.memory with registers }⟩, updated))
  let request kind index input := queryFromRegisters kind (state.memory.registers index) (state.memory.registers input)
  let write first second query answer :=
    let values := answerWords query answer
    Function.update (Function.update state.memory.registers first values.1) second values.2
  match machine.code[state.pc.val] with
  | .compute _ => (BoundedMachine.step machine.arithmetic state).map
      (Option.map fun result => (result.1, result.2, oracle))
  | .query kind index input first second next =>
      match request kind index input with
      | none => PMF.pure none
      | some query => (LazyOracle.query query oracle).map
          (fun answer => resume next (write first second query answer.1) answer.2)
  | .lookup kind index input first second present next =>
      match request kind index input with
      | none => PMF.pure none
      | some query => PMF.pure (match LazyOracle.lookup query oracle with
          | none => resume next (Function.update state.memory.registers present 0) oracle
          | some answer => resume next (Function.update (write first second query answer) present 1) oracle)
  | .program kind index input first second next =>
      match request kind index input with
      | none => PMF.pure none
      | some query => PMF.pure ((LazyOracle.program query
          (answerFromWords query (state.memory.registers first) (state.memory.registers second)) oracle).map
            (fun updated => (false, (⟨next, state.memory⟩, updated))))

/-- The interpreter charges each instruction against the selected stage fuel. -/
noncomputable def Simulator.run [BN254.FieldCertificate]
    {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex]
    [DecidableEq FixedIndex] [DecidableEq EncIndex] (machine : Simulator) :
    Nat → Configuration (machine.size + 1) → LazyOracle.State FixedIndex EncIndex →
      PMF (Option (Configuration (machine.size + 1) × LazyOracle.State FixedIndex EncIndex × Nat))
  | 0, _, _ => PMF.pure none
  | fuel + 1, state, oracle => (machine.step state oracle).bind fun outcome =>
      match outcome with
      | none => PMF.pure none
      | some (true, next, updated) => PMF.pure (some (next, updated, 1))
      | some (false, next, updated) => (machine.run fuel next updated).map
          (Option.map fun result => (result.1, result.2.1, result.2.2 + 1))

/-- The lifted arithmetic step leaves the external oracle unchanged. -/
theorem Simulator.ofMachine_step [BN254.FieldCertificate]
    {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex]
    [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (machine : Machine) (firstFuel secondFuel : Nat)
    (within : machine.size + 1 + firstFuel + secondFuel ≤ 2 ^ 60)
    (state : Configuration (machine.size + 1)) (oracle : LazyOracle.State FixedIndex EncIndex) :
    (Simulator.ofMachine machine firstFuel secondFuel within).step state oracle =
      (BoundedMachine.step machine state).map (Option.map fun result => (result.1, result.2, oracle)) := by
  simp only [Simulator.step, Simulator.ofMachine, Vector.getElem_map]
  congr 2
  exact Simulator.ofMachine_arithmetic machine firstFuel secondFuel within

/-- Every successful simulator run stays within its supplied fuel. -/
theorem Simulator.run_cost [BN254.FieldCertificate]
    {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex]
    [DecidableEq FixedIndex] [DecidableEq EncIndex] (machine : Simulator) (fuel : Nat)
    (state result : Configuration (machine.size + 1))
    (oracle updated : LazyOracle.State FixedIndex EncIndex) (cost : Nat)
    (member : some (result, updated, cost) ∈ (machine.run fuel state oracle).support) : cost ≤ fuel := by
  induction fuel generalizing state result oracle updated cost with
  | zero => simp [run] at member
  | succ fuel ih =>
    simp only [run, PMF.mem_support_bind_iff] at member
    obtain ⟨outcome, _, member⟩ := member
    cases outcome with
    | none => simp at member
    | some outcome =>
      rcases outcome with ⟨halted, next, updated⟩
      cases halted with
      | true => simp at member; omega
      | false =>
        rw [PMF.support_map] at member
        obtain ⟨value, supported, same⟩ := member
        cases value with
        | none => simp at same
        | some value =>
          cases same
          exact Nat.add_le_add_right (ih next value.1 updated value.2.1 value.2.2 supported) 1

/-- The lifted arithmetic run has the same result and cost. -/
theorem Simulator.ofMachine_run [BN254.FieldCertificate]
    {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex]
    [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (machine : Machine) (firstFuel secondFuel : Nat)
    (within : machine.size + 1 + firstFuel + secondFuel ≤ 2 ^ 60)
    (fuel : Nat) (state : Configuration (machine.size + 1)) (oracle : LazyOracle.State FixedIndex EncIndex) :
    (Simulator.ofMachine machine firstFuel secondFuel within).run fuel state oracle =
      (BoundedMachine.run machine fuel state).map (Option.map fun result => (result.1, oracle, result.2)) := by
  induction fuel generalizing state with
  | zero => rw [Simulator.run.eq_def, BoundedMachine.run, PMF.pure_map]; rfl
  | succ fuel ih =>
    rw [Simulator.run.eq_def]; dsimp only; rw [ofMachine_step, PMF.bind_map, BoundedMachine.run, PMF.map_bind]
    congr 1
    funext outcome
    cases outcome with
    | none => simp [PMF.pure_map]
    | some outcome =>
      rcases outcome with ⟨halted, next⟩
      cases halted <;> simp [PMF.pure_map, ih, PMF.map_comp, Function.comp_def]

theorem step_halt [BN254.FieldCertificate] (machine : Machine)
    (state next : Configuration (machine.size + 1))
    (member : some (true, next) ∈ (step machine state).support) :
    machine.code[state.pc.val] = .halt ∧ next = state := by
  unfold step at member
  generalize equal : machine.code[state.pc.val] = instruction at member
  cases instruction <;> simp_all
  split at member <;> simp_all
  split at member <;> simp_all

theorem run_positive [BN254.FieldCertificate] (machine : Machine) (fuel : Nat)
    (state next : Configuration (machine.size + 1)) (cost : Nat)
    (member : some (next, cost) ∈ (run machine fuel state).support) : 0 < cost := by
  cases fuel with
  | zero => simp [run] at member
  | succ fuel =>
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
        obtain ⟨value, _, same⟩ := member
        cases value <;> simp_all
        omega

/-- The arithmetic interpreter stops before each external oracle instruction. -/
theorem Simulator.run_arithmetic_prefix [BN254.FieldCertificate]
    {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex]
    [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (machine : Simulator) (fuel : Nat) (state : Configuration (machine.size + 1))
    (oracle : LazyOracle.State FixedIndex EncIndex) :
    machine.run fuel state oracle =
      (BoundedMachine.run machine.arithmetic fuel state).bind (fun result => match result with
        | none => PMF.pure none
        | some (next, cost) => (machine.run (fuel - cost + 1) next oracle).map
            (Option.map fun result => (result.1, result.2.1, result.2.2 + cost - 1))) := by
  induction fuel generalizing state with
  | zero => simp [Simulator.run, BoundedMachine.run, PMF.pure_bind]
  | succ fuel ih =>
    generalize code : machine.code[state.pc.val] = instruction
    cases instruction with
    | compute instruction =>
      rw [Simulator.run, BoundedMachine.run, PMF.bind_bind]
      simp only [Simulator.step, code, PMF.bind_map]
      apply PMF.bind_congr
      intro outcome supported
      cases outcome with
      | none => simp [PMF.pure_bind]
      | some outcome =>
        rcases outcome with ⟨halted, next⟩
        cases halted with
        | true =>
          obtain ⟨halt, rfl⟩ := step_halt machine.arithmetic state next supported
          have halted : instruction = .halt := by simpa [Simulator.arithmetic, code] using halt
          subst instruction
          simp [PMF.pure_bind, Simulator.run, Simulator.step, code,
            BoundedMachine.step, Simulator.arithmetic, PMF.pure_map]
        | false =>
          dsimp only [Function.comp_apply, Option.map]
          rw [ih, PMF.map_bind, PMF.bind_map]
          apply PMF.bind_congr
          intro result member
          cases result with
          | none => simp [PMF.pure_map]
          | some result =>
            rcases result with ⟨next, cost⟩
            have positive := run_positive machine.arithmetic fuel _ next cost member
            simp only [Option.map_some, Nat.add_sub_add_right, PMF.map_comp, Function.comp_def]
            congr 1
            funext result
            cases result with
            | none => rfl
            | some result =>
                simp only [Option.map_some]
                congr 3
                omega
    | query | lookup | program =>
      simp [BoundedMachine.run, BoundedMachine.step, Simulator.arithmetic, code,
        PMF.pure_bind, PMF.map_id]

/-- A proved arithmetic prefix retains its exact simulator continuation and cost. -/
theorem Simulator.run_prefix [BN254.FieldCertificate]
    {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex]
    [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (machine : Simulator) (cost fuel : Nat)
    (start finish : Configuration (machine.size + 1)) (oracle : LazyOracle.State FixedIndex EncIndex)
    (agreement : BoundedMachine.run machine.arithmetic (cost + fuel) start =
      (BoundedMachine.run machine.arithmetic fuel finish).map
        (Option.map fun result => (result.1, result.2 + cost))) :
    machine.run (cost + fuel) start oracle =
      (machine.run fuel finish oracle).map
        (Option.map fun result => (result.1, result.2.1, result.2.2 + cost)) := by
  rw [machine.run_arithmetic_prefix (cost + fuel) start oracle,
    machine.run_arithmetic_prefix fuel finish oracle, agreement, PMF.bind_map, PMF.map_bind]
  apply PMF.bind_congr
  intro result member
  cases result with
  | none => simp [PMF.pure_map]
  | some result =>
    rcases result with ⟨next, spent⟩
    have positive := run_positive machine.arithmetic fuel finish next spent member
    have remaining : cost + fuel - (spent + cost) + 1 = fuel - spent + 1 := by omega
    simp only [Function.comp_apply, Option.map_some, remaining, PMF.map_comp]
    congr 1
    funext result
    cases result with
    | none => rfl
    | some result =>
        simp only [Function.comp_apply, Option.map_some]
        congr 3
        omega
end Kriterion.Cryptography.BoundedMachine
