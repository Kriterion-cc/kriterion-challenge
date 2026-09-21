import Benchmark
import PaperFormulaChecks
import Lean

example (solution : Kriterion.Solution)
    (field : Kriterion.BN254.FieldCertificate)
    (group : @Kriterion.BN254.GroupCertificate field) (parameter : Nat)
    (scalar : Kriterion.BN254.NonZeroScalar) (tape : solution.Randomness × Kriterion.Cryptography.PublicOracle solution.FixedIndex solution.EncIndex) :
    (solution.encoding.encode ((solution.garbleProgram field group parameter scalar tape.1).eval
      (Kriterion.Cryptography.publicAnswer tape.2)).1).length =
      Kriterion.Benchmark.ciphertextBytes solution := by
  rw [solution.garbleProgramCorrect]
  exact solution.ciphertextSize field group parameter scalar tape

example (solution : Kriterion.Solution) (circuit : solution.Public) :
    solution.encoding.decode (solution.encoding.encode circuit) = some (circuit, []) := by
  simpa using solution.encoding.decode_encode circuit []

-- The decoder prevents an encoding from hiding different public values.
example (encoding : Kriterion.Encoding Bool) :
    encoding.encode true ≠ encoding.encode false := by
  intro same
  have left := encoding.decode_encode true []
  have right := encoding.decode_encode false []
  rw [same] at left
  simp only [List.append_nil] at left right
  rw [right] at left
  cases left

-- The byte encoding uses little-endian order.
example : (Kriterion.Encoding.natural 2).encode ⟨258, by decide⟩ = [2, 1] := by decide

-- The decoder rejects a missing byte.
example : (Kriterion.Encoding.natural 2).decode [2] = none := by decide

-- The option decoder rejects an unknown tag.
example : (Kriterion.Encoding.option Kriterion.Encoding.byte).decode [2] = none := by decide

-- The eager interpreter returns the same answer for a repeated query.
example (tape : Fin 2 → Fin 2) (input : Fin 2) :
    Kriterion.Cryptography.randomOracleAnswer tape input = tape input := rfl

-- The lazy oracle preserves a complete cache.
example (tape : Fin 2 → Fin 2) (input : Fin 2) :
    (OracleSpec.randomOracle (spec := Fin 2 →ₒ Fin 2) input).run
        (fun value => some (tape value)) =
      pure (tape input, fun value => some (tape value)) :=
  Kriterion.Cryptography.randomOracle_complete tape input

-- A simulator cannot program a pair that a prior query uses.
example (value : Kriterion.Cryptography.Block) :
    ¬ Kriterion.Cryptography.FreshPermutationPair
      [⟨.forward, .adversary, (), value, value⟩] () value value := by
  intro fresh
  exact (fresh ⟨.forward, .adversary, (), value, value⟩ (List.mem_singleton_self _) rfl).1 rfl

namespace OracleProgramRegression

open Kriterion.Cryptography

universe uQuery uAnswer uResult uState

/-- This reference preserves the execution rules from before the VCV-io migration. -/
private noncomputable def reference {oracle : OracleSpec.{uQuery, uAnswer}}
    {Result : Type uResult} {State : Type uState} (handler : OracleHandler oracle State) :
    {budget : Nat} → OracleProgram oracle Result budget → State → PMF (Result × State)
  | _, .pure result, state => result.map fun value => (value, state)
  | _, .query request next, state =>
      let answer := handler request state
      reference handler (next answer.1) answer.2
  | _, .sample distribution next, state =>
      distribution.bind fun value => reference handler (next value) state

/-- VCV-io preserves every result and final state for every program and PMF sample. -/
theorem execution_eq_reference {oracle : OracleSpec.{uQuery, uAnswer}}
    {Result : Type uResult} {State : Type uState} (handler : OracleHandler oracle State)
    {budget : Nat} (program : OracleProgram oracle Result budget) (state : State) :
    program.run handler state = reference handler program state := by
  induction program generalizing state with
  | pure distribution => simp [reference]
  | query request next ih => simpa [reference] using ih (handler request state).1 (handler request state).2
  | sample distribution next ih => simp [reference, ih]

end OracleProgramRegression

namespace MachineRegression

open Kriterion.Cryptography.BoundedMachine Kriterion.GarbledCircuit.SimulatorProtocol

variable [Kriterion.BN254.FieldCertificate]

-- The machine cannot terminate a loop within any finite budget.
private def loop : Machine := ⟨0, #v[.push 0 false 0], by decide⟩
private theorem loop_aborts (fuel : Nat) (state : Configuration (loop.size + 1)) :
    run loop fuel state = PMF.pure none := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    rcases state with ⟨pc, memory⟩
    have only : pc = 0 := by
      apply Fin.ext
      have bound := pc.isLt
      change pc.val < 1 at bound
      change pc.val = 0
      omega
    subst pc
    simp only [run]
    have next : step loop ⟨0, memory⟩ = PMF.pure (some (false,
        ⟨0, { memory with bits := Function.update memory.bits 0 (false :: memory.bits 0) }⟩)) := rfl
    rw [next, PMF.pure_bind]
    simp only [ih, PMF.pure_map, Option.map_none]

-- The word instructions have fixed width. Each field instruction uses its own modulus.
example : Arithmetic.eval .add (BitVec.ofNat 256 (2 ^ 256 - 1)) 1 = 0 := by decide
example : Arithmetic.eval .fieldSub 0 1 =
    BitVec.ofNat 256 (Kriterion.BN254.baseFieldModulus - 1) := by decide
example : Arithmetic.eval .scalarSub 0 1 =
    BitVec.ofNat 256 (Kriterion.BN254.scalarFieldModulus - 1) := by decide
example : Arithmetic.eval .fieldInv 0 0 = 0 := by simp [Arithmetic.eval]

-- The program must read the stored value after it overwrites the source register.
private def arithmeticProgram : Machine := ⟨6, #v[
  .constant 0 9 1, .constant 1 40 2, .store 0 1 3, .constant 1 2 4,
  .load 2 0 5, .arithmetic .add 3 1 2 6, .halt], by decide⟩

example : (run arithmeticProgram 7 ⟨0, {}⟩).map
    (Option.map fun result => (result.1.memory.registers 3, result.2)) =
      PMF.pure (some (42, 7)) := by
  simp [run, step, arithmeticProgram, Arithmetic.eval, Function.update, PMF.pure_bind, PMF.pure_map]

-- The halt consumes the seventh unit.
example : run arithmeticProgram 6 ⟨0, {}⟩ = PMF.pure none := by
  simp [run, step, arithmeticProgram, Arithmetic.eval, Function.update, PMF.pure_bind, PMF.pure_map]

-- The group instruction rejects an invalid tag.
example : readPoint (fun _ => 2) ⟨0, 1, 2⟩ = none := by
  simp [readPoint]

-- The group program adds two identity points and charges its halt.
private def groupProgram : Machine :=
  ⟨1, #v[.pointAdd ⟨6, 7, 8⟩ ⟨0, 1, 2⟩ ⟨3, 4, 5⟩ 1, .halt], by decide⟩

example : (run groupProgram 2 ⟨0, {}⟩).map
    (Option.map fun result => (readPoint result.1.memory.registers ⟨6, 7, 8⟩, result.2)) =
      PMF.pure (some (some 0, 2)) := by
  simp [run, step, groupProgram, readPoint, writePoint, Function.update, PMF.pure_bind, PMF.pure_map]

-- The group instruction rejects a noncanonical affine coordinate.
example : readPoint
    (fun i => if i = 0 then 1 else BitVec.ofNat 256 Kriterion.BN254.baseFieldModulus)
    ⟨0, 1, 2⟩ = none := by
  norm_num [readPoint, Kriterion.BN254.baseFieldModulus, BitVec.toNat_ofNat]
  intro impossible
  exact False.elim ((by decide : (1 : Word) ≠ 0) impossible)

-- The parser rejects short replies and reads each byte in little-endian order.
example : words 8 1 [true] = none := by decide
example : (words 8 1 [true, false, true, false, false, false, false, false]).map
    (fun values => values[0].toNat) = some 5 := by decide

-- The public decoder cannot substitute different bytes for a machine reply.
private def permissive : Kriterion.Encoding Unit where
  encode _ := [0]
  decode wire := match wire with | [] => none | _ :: tail => some ((), tail)
  decode_encode _ _ := rfl

example : publicValue permissive 1 [false, false, false, false, false, false, false, false] =
    some () := by simp [publicValue, words, permissive, Vector.toList_ofFn, List.ofFn_succ]
example : publicValue permissive 1 [true, false, false, false, false, false, false, false] =
    none := by
  simp [publicValue, words, permissive, Vector.toList_ofFn, List.ofFn_succ]
  decide

end MachineRegression

-- The wire type excludes any extra transmitted payload.
example (solution : Kriterion.Solution) (field : Kriterion.BN254.FieldCertificate)
    (group : @Kriterion.BN254.GroupCertificate field) (key : solution.EncodingKey)
    (input : Kriterion.BN254.AffineInput) :
    (((solution.scheme field group).encode key input).toList).length = 508 := by simp

-- The real handler exposes the evaluator's inverse permutation and preserves its tape.
example (solution : Kriterion.Solution) (tape : solution.Randomness × Kriterion.Cryptography.PublicOracle solution.FixedIndex solution.EncIndex)
    (index : solution.FixedIndex) (input : Kriterion.Cryptography.Block) :
    Kriterion.Cryptography.publicHandler (Prod.snd : solution.Randomness × Kriterion.Cryptography.PublicOracle solution.FixedIndex solution.EncIndex → _)
      (.fixedInverse index (tape.2.1.permutation index input)) tape =
      (input, tape) := by
  simp only [Kriterion.Cryptography.publicHandler, Kriterion.Cryptography.publicAnswer,
    Equiv.symm_apply_apply]
  rfl

private theorem originInvalid : Kriterion.BN254.validate ⟨0, 0⟩ = false := by decide

-- Correct evaluation rejects the off-curve origin for every scalar and tape.
example (solution : Kriterion.Solution) (field : Kriterion.BN254.FieldCertificate)
    (group : @Kriterion.BN254.GroupCertificate field) (scalar : Kriterion.BN254.NonZeroScalar)
    (tape : solution.Randomness × Kriterion.Cryptography.PublicOracle solution.FixedIndex solution.EncIndex) :
    let scheme := solution.scheme field group
    let circuit := (solution.garbleProgram field group 100 scalar tape.1).eval
      (Kriterion.Cryptography.publicAnswer tape.2)
    (solution.evaluateProgram field group circuit.1 ⟨0, 0⟩
      (scheme.encode circuit.2 ⟨0, 0⟩)).eval (Kriterion.Cryptography.publicAnswer tape.2) = some none := by
  letI := field
  letI := group
  dsimp only
  rw [solution.garbleProgramCorrect, solution.evaluateProgramCorrect,
    solution.perfectCorrectness field group 100 scalar tape ⟨0, 0⟩, solution.functionCorrect]
  simp [Kriterion.checkedScalarMultiplication, Kriterion.BN254.decodePoint, originInvalid]

namespace MachineAdversaryTests
open Kriterion Kriterion.Cryptography Kriterion.Cryptography.BoundedMachine

private def haltMachine : Adversary := ⟨0, #v[.compute .halt], by decide, 1, 1⟩
private def query : Adversary := ⟨1, #v[.query 4 0 0 0 1 1, .compute .halt], by decide, 2, 2⟩
private def handler : OracleHandler (publicOracleSpec Empty Empty) Unit :=
  fun request state => match request with
  | .hash _ => ((0, 0), state)
  | .fixedForward index _ | .fixedInverse index _ => nomatch index
  | .encForward index _ | .encInverse index _ => nomatch index

example [BN254.FieldCertificate] :
    ((haltMachine.program 0 ⟨0, {}⟩).run handler ()).map Prod.fst = PMF.pure none := by
  simp [Adversary.program, OracleProgram.run_pure, PMF.pure_map]

set_option backward.isDefEq.respectTransparency false in
example [BN254.FieldCertificate] :
    (haltMachine.program 1 ⟨0, {}⟩).run handler () = PMF.pure (some (⟨0, {}⟩ : Configuration 1), ()) := by
  simp [Adversary.program, Adversary.arithmetic, haltMachine, step,
    OracleProgram.run_sample, OracleProgram.run_pure, PMF.pure_bind, PMF.pure_map]

example [BN254.FieldCertificate] :
    ((query.program 1 ⟨0, {}⟩).run handler ()).map Prod.fst = PMF.pure none := by
  change ((OracleProgram.query (oracle := publicOracleSpec Empty Empty) (budget := 0) (.hash 0)
    (fun _ => OracleProgram.pure (PMF.pure (none : Option (Configuration 2))))).run handler ()).map Prod.fst = _
  simp only [OracleProgram.run_query, OracleProgram.run_pure, PMF.pure_map]
  rfl

end MachineAdversaryTests

namespace Kriterion.LazyOracleTests
open Cryptography Cryptography.LazyOracle ArgoMAC.Security.OperationalOracle

example (state : SparsePermutation (2 ^ 128)) (input : Block)
    (answer : Fin (2 ^ 128) × SparsePermutation (2 ^ 128))
    (member : answer ∈ (state.forward input.toFin).distribution.support) :
    answer.2.forward input.toFin = Draw.pure (answer.1, answer.2) :=
  lookup_forward _ _ _ (forward_lookup _ _ _ member)

example (state : SparsePermutation (2 ^ 128)) (input : Block)
    (answer : Fin (2 ^ 128) × SparsePermutation (2 ^ 128))
    (member : answer ∈ (state.forward input.toFin).distribution.support) :
    answer.2.inverse answer.1 = Draw.pure (input.toFin, answer.2) := by
  rw [SparsePermutation.inverse_reverse_forward,
    lookup_forward _ _ _ (lookup_inverse _ _ _ (forward_lookup _ _ _ member))]
  rfl

example : ((permutationProgram (.empty 2) 0 1).bind
    (fun state => permutationProgram state 0 0)) = none := by decide

example : ((permutationProgram (.empty 2) 0 1).bind
    (fun state => permutationProgram state 1 1)) = none := by decide

example : ((program (.hash 0) (0, 0) (empty : State Empty Empty)).bind
    (program (.hash 1) (0, 0))).isSome = true := by
  have distinct : ((1 : BN254.BaseField) == 0) = false := by decide
  simp [program, empty, HashTable.program, List.lookup, distinct]

example : ((program (.hash 0) (0, 0) (empty : State Empty Empty)).bind
    (program (.hash 0) (1, 1))) = none := by
  simp [program, empty, HashTable.program, List.lookup]

end Kriterion.LazyOracleTests

namespace HashPadRegression
open Kriterion Kriterion.Cryptography

-- The reported entry uses this recurrence at ed8f1afaf80641fc609ec4c2da5617f2a7cb2db6.
private def hashPadPrefix (table : BN254.BaseField → Block × Block) : Nat → Block × Block
  | 0 => (0, 0)
  | n + 1 => let pad := hashPadPrefix table n; let value := table n
    (pad.1 ^^^ value.1, pad.2 ^^^ value.2)

-- Each query node replaces one table read in the reported recurrence.
private def program : (n : Nat) → QueryProgram (publicOracleSpec Empty Empty) (Block × Block) n
  | 0 => .pure (0, 0)
  | n + 1 => .query (.hash n) fun value =>
      (program n).map fun pad => (pad.1 ^^^ value.1, pad.2 ^^^ value.2)

private def queriesUsed {oracle : OracleSpec.{0, 0}} {Result : Type}
    (answer : ∀ q, oracle.Answer q) : {budget : Nat} → QueryProgram oracle Result budget → Nat
  | _, .pure _ => 0
  | _, .query request next => queriesUsed answer (next (answer request)) + 1

private theorem queriesUsed_le {oracle : OracleSpec.{0, 0}} {Result : Type}
    (answer : ∀ q, oracle.Answer q) {budget : Nat} (computation : QueryProgram oracle Result budget) :
    queriesUsed answer computation ≤ budget := by
  induction computation with
  | pure => exact Nat.zero_le _
  | query request next ih => exact Nat.add_le_add_right (ih (answer request)) 1

private theorem queriesUsed_map {oracle : OracleSpec.{0, 0}} {First Second : Type}
    (answer : ∀ q, oracle.Answer q) (f : First → Second) {budget : Nat}
    (computation : QueryProgram oracle First budget) :
    queriesUsed answer (computation.map f) = queriesUsed answer computation := by
  induction computation with
  | pure => rfl
  | query request next ih => exact congrArg (· + 1) (ih (answer request))

-- The query program returns the same pad for every oracle and prefix length.
example (oracle : PublicOracle Empty Empty) (n : Nat) :
    (program n).eval (publicAnswer oracle) = hashPadPrefix oracle.2.2 n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [program, QueryProgram.eval, QueryProgram.eval_map, publicAnswer,
        hashPadPrefix, ih]
      rfl

private theorem program_queries (answer : ∀ q : PublicQuery Empty Empty, q.Answer) (n : Nat) :
    queriesUsed answer (program n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [program, queriesUsed, queriesUsed_map, ih]

-- The exact reported prefix exceeds both baseline query limits.
example (answer : ∀ q : PublicQuery Empty Empty, q.Answer) :
    ¬ queriesUsed answer (program (2 ^ 101)) ≤ 1759967 ∧
    ¬ queriesUsed answer (program (2 ^ 101)) ≤ 1055879 := by
  rw [program_queries]
  constructor <;> norm_num

-- No indexed program with either limit can execute the same number of queries.
example {budget : Nat} (bounded : budget ≤ 1759967)
    (answer : ∀ q : PublicQuery Empty Empty, q.Answer)
    (computation : QueryProgram (publicOracleSpec Empty Empty) (Block × Block) budget) :
    queriesUsed answer computation ≠ queriesUsed answer (program (2 ^ 101)) := by
  have limit := queriesUsed_le answer computation
  rw [program_queries]
  have large : 1759967 < 2 ^ 101 := by norm_num
  omega

end HashPadRegression

-- The shared library must not introduce an unproved assumption.
run_cmd do
  let env ← Lean.getEnv
  for (name, _) in env.constants.toList do
    if (`Kriterion).isPrefixOf name || (`OracleProgramRegression).isPrefixOf name ||
        (`MachineRegression).isPrefixOf name ||
        (env.getModuleIdxFor? name).isNone then
      let illegal := (← Lean.collectAxioms name).filter fun axiomName =>
        !#[`propext, `Classical.choice, `Quot.sound].contains axiomName
      unless illegal.isEmpty do Lean.throwError m!"The declaration {name} uses disallowed axioms: {illegal}"
