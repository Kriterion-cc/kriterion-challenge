import Benchmark
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
        (env.getModuleIdxFor? name).isNone then
      let illegal := (← Lean.collectAxioms name).filter fun axiomName =>
        !#[`propext, `Classical.choice, `Quot.sound].contains axiomName
      unless illegal.isEmpty do Lean.throwError "disallowed axioms in {name}: {illegal}"
