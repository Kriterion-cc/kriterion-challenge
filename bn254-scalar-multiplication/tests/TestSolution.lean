import Benchmark
import PaperFormulaChecks
import Lean

example (solution : Kriterion.Solution)
    (field : Kriterion.BN254.FieldCertificate)
    (group : @Kriterion.BN254.GroupCertificate field) (parameter : Nat)
    (scalar : Kriterion.BN254.NonZeroScalar) (tape : solution.Randomness) :
    (solution.encoding.encode ((solution.scheme field group).garble parameter scalar tape).1).length =
      Kriterion.Benchmark.ciphertextBytes solution :=
  solution.ciphertextSize field group parameter scalar tape

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

-- The next request cannot reset an exhausted budget.
example (machine : Machine) (request : List Bool) (state : State)
    (exhausted : state.spent = budget state.queries) :
    respond machine request state = PMF.pure none := by
  simp [respond, exhausted, run, PMF.pure_map]

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
example (solution : Kriterion.Solution) (tape : solution.Randomness)
    (index : solution.FixedIndex) (input : Kriterion.Cryptography.Block) :
    Kriterion.Cryptography.publicHandler solution.evaluationOracle
      (.fixedInverse index ((solution.evaluationOracle tape).1.permutation index input)) tape =
      (input, tape) := by
  simp only [Kriterion.Cryptography.publicHandler, Kriterion.Cryptography.publicAnswer,
    Equiv.symm_apply_apply]
  rfl

private theorem originInvalid : Kriterion.BN254.validate ⟨0, 0⟩ = false := by decide

-- Correct evaluation rejects the off-curve origin for every scalar and tape.
example (solution : Kriterion.Solution) (field : Kriterion.BN254.FieldCertificate)
    (group : @Kriterion.BN254.GroupCertificate field) (scalar : Kriterion.BN254.NonZeroScalar)
    (tape : solution.Randomness) :
    let scheme := solution.scheme field group
    let circuit := scheme.garble 100 scalar tape
    scheme.evaluate (solution.evaluationOracle tape) circuit.1 ⟨0, 0⟩
      (scheme.encode circuit.2 ⟨0, 0⟩) = some none := by
  letI := field
  letI := group
  dsimp only
  rw [solution.perfectCorrectness field group 100 scalar tape ⟨0, 0⟩, solution.functionCorrect]
  simp [Kriterion.checkedScalarMultiplication, Kriterion.BN254.decodePoint, originInvalid]

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
