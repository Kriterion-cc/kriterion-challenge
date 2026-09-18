import GarbledCircuit
import Cryptography.Assumptions
import Cryptography.BoundedMachine
import Encoding
import Mathlib.Data.Fintype.EquivFin

/-!
This module defines the adaptive games.
The [BaBe source](https://github.com/babylonlabs-io/BaBe.latex/blob/e2dcf4d540b2708e13cd21090df759051119a116/Latex/preliminaries.tex) fixes the paper references below.
-/

namespace Kriterion.GarbledCircuit

open Cryptography.Assumptions
open Cryptography

/-- This invariant enforces the public interface and preserves earlier answers.
See `gc_rpm_proof.tex`, "Transcripts and Compatibility", and
`preliminaries.tex`, `def:pRPM`. The challenge also checks the simulator's state updates. -/
def OracleSimulation {FixedIndex EncIndex Input Output Public Labels Topology State : Type}
    (simulator : Simulator Input Output Public Labels Topology State)
    (handler : OracleHandler (publicOracleSpec FixedIndex EncIndex) State)
    (view : State → PublicOracle FixedIndex EncIndex) : Prop :=
  ∃ valid : State → Prop, ∃ seen : State → PublicQuery FixedIndex EncIndex → Prop,
    (∀ parameter topology result, result ∈ (simulator.simulateGarble parameter topology).support →
      valid result.2) ∧
    (∀ query state, valid state →
      (handler query state).1 = publicAnswer (view state) query ∧
      view (handler query state).2 = view state ∧ valid (handler query state).2 ∧
      seen (handler query state).2 query ∧
      ∀ prior, seen state prior → seen (handler query state).2 prior) ∧
    (∀ state input output result, valid state →
      result ∈ (simulator.simulateEncode state input output).support →
      valid result.2 ∧ ∀ query, seen state query →
        seen result.2 query ∧ publicAnswer (view result.2) query = publicAnswer (view state) query)

/-- A label adapter preserves every oracle-state obligation. -/
theorem OracleSimulation.mapLabels {FixedIndex EncIndex Input Output Public Labels Topology
    State Wire NewTopology : Type}
    {simulator : Simulator Input Output Public Labels Topology State}
    {handler : OracleHandler (publicOracleSpec FixedIndex EncIndex) State}
    {view : State → PublicOracle FixedIndex EncIndex}
    (rules : OracleSimulation simulator handler view)
    (pack : Labels → Wire) (restore : NewTopology → Topology) :
    OracleSimulation (simulator.mapLabels pack restore) handler view := by
  obtain ⟨valid, seen, initial, query, encode⟩ := rules
  refine ⟨valid, seen, fun parameter topology => initial parameter (restore topology), query, ?_⟩
  intro state input output result stateValid member
  dsimp only [Simulator.mapLabels] at member
  rw [PMF.support_map] at member
  obtain ⟨original, originalMember, rfl⟩ := member
  exact encode state input output original stateValid originalMember

universe u uAux

/-- An adaptive adversary selects its input after it receives the public circuit. -/
structure AdaptiveAdversary
    (oracle : OracleSpec) (Input Public Labels : Type u) (Aux : Type uAux) where
  State : Type u
  /-- The first budget counts public queries before the input choice. -/
  firstQueryBudget : Nat → Nat
  /-- The second budget counts public queries after the labels arrive. -/
  secondQueryBudget : Nat → Nat
  /-- The adversary chooses the input after the ciphertext in `def:garbling-scheme`. -/
  chooseInput : (parameter : Nat) → Public → Aux →
    OracleProgram oracle (Input × State) (firstQueryBudget parameter)
  /-- The final bit defines the distinguishing event in `def:garbling-scheme`. -/
  decide : (parameter : Nat) → Public → Labels → Aux → State →
    OracleProgram oracle Bool (secondQueryBudget parameter)

/-- This challenge convention counts public queries plus one decision step.
The count excludes local computation and private sampling. It does not model PPT running time. -/
def adversaryWork {oracle : OracleSpec} {Input Public Labels : Type u} {Aux : Type uAux}
    (adversary : AdaptiveAdversary oracle Input Public Labels Aux) (parameter : Nat) : Nat :=
  adversary.firstQueryBudget parameter + adversary.secondQueryBudget parameter + 1

/-- The real experiment follows `preliminaries.tex`, `def:garbling-scheme`, Adaptive Privacy.
The same sampled tape supplies the garbler and both adversary stages. -/
noncomputable def realGame
    {oracle : OracleSpec} {Circuit Input Output Randomness Public EncodingKey Labels
      EvaluationOracle : Type u} {Aux : Type uAux}
    (scheme : GarbledCircuit Circuit Input Output Randomness Public EncodingKey Labels EvaluationOracle)
    (randomTape : Nat → PMF Randomness)
    (oracleHandler : OracleHandler oracle Randomness)
    (adversary : AdaptiveAdversary oracle Input Public Labels Aux)
    (parameter : Nat) (circuit : Circuit) (auxiliary : Aux) : PMF Bool :=
  PMF.bind (randomTape parameter) fun randomness =>
    let garbled := scheme.garble parameter circuit randomness
    PMF.bind ((adversary.chooseInput parameter garbled.1 auxiliary).run oracleHandler randomness)
      fun selected => PMF.map Prod.fst
        ((adversary.decide parameter garbled.1 (scheme.encode garbled.2 selected.1.1)
          auxiliary selected.1.2).run oracleHandler selected.2)

/-- The ideal experiment follows `preliminaries.tex`, `def:garbling-scheme`, Adaptive Privacy.
The second simulator stage receives the selected input and target output. -/
noncomputable def idealGame
    {oracle : OracleSpec}
    {Circuit Input Output Randomness Public EncodingKey Labels EvaluationOracle Topology State : Type u}
    {Aux : Type uAux}
    (scheme : GarbledCircuit Circuit Input Output Randomness Public EncodingKey Labels EvaluationOracle)
    (topology : Circuit → Topology)
    (simulator : Simulator Input Output Public Labels Topology State)
    (oracleHandler : OracleHandler oracle State)
    (adversary : AdaptiveAdversary oracle Input Public Labels Aux)
    (parameter : Nat) (circuit : Circuit) (auxiliary : Aux) : PMF Bool :=
  PMF.bind (simulator.simulateGarble parameter (topology circuit)) fun simulated =>
    PMF.bind ((adversary.chooseInput parameter simulated.1 auxiliary).run
      oracleHandler simulated.2) fun selected =>
      PMF.bind (simulator.simulateEncode selected.2 selected.1.1
        (scheme.function circuit selected.1.1)) fun encoded =>
        PMF.map Prod.fst ((adversary.decide parameter simulated.1 encoded.1 auxiliary
          selected.1.2).run oracleHandler encoded.2)

/-- This helper bounds the distance between two abstract experiments.
The final adaptive privacy property also requires a bounded machine. -/
def ConcreteAdaptivePrivacy
    {oracle : OracleSpec}
    {Circuit Input Output Randomness Public EncodingKey Labels EvaluationOracle Topology State : Type u}
    {Aux : Type uAux}
    (scheme : GarbledCircuit Circuit Input Output Randomness Public EncodingKey Labels EvaluationOracle)
    (topology : Circuit → Topology)
    (simulator : Simulator Input Output Public Labels Topology State)
    (randomTape : Nat → PMF Randomness)
    (realOracle : OracleHandler oracle Randomness)
    (idealOracle : OracleHandler oracle State)
    (bits : Nat) : Prop :=
  ∀ adversary, ∀ circuit : Nat → Circuit, ∀ auxiliary : Nat → Aux, ∀ parameter,
    WorkPerAdvantage bits (adversaryWork adversary parameter)
      (advantage
        (realGame scheme randomTape realOracle adversary parameter
          (circuit parameter) (auxiliary parameter))
        (idealGame scheme topology simulator idealOracle adversary parameter
          (circuit parameter) (auxiliary parameter)))

/-- A public label map preserves the bound in `preliminaries.tex`, `def:garbling-scheme`.
The adapter may also replace the simulator's topology representation. -/
theorem ConcreteAdaptivePrivacy.mapLabels
    {oracle : OracleSpec} {Circuit Input Output Randomness Public Key Labels Wire
      EvaluationOracle Topology NewTopology State Aux : Type}
    {scheme : GarbledCircuit Circuit Input Output Randomness Public Key Labels EvaluationOracle}
    {topology : Circuit → Topology} {simulator : Simulator Input Output Public Labels Topology State}
    {randomTape : Nat → PMF Randomness} {realOracle : OracleHandler oracle Randomness}
    {idealOracle : OracleHandler oracle State} {bits : Nat}
    (privacy : ConcreteAdaptivePrivacy (Aux := Aux) scheme topology simulator randomTape
      realOracle idealOracle bits)
    (pack : Labels → Wire) (unpack : Input → Wire → Labels)
    (newTopology : Circuit → NewTopology) (restore : NewTopology → Topology)
    (same : ∀ circuit, restore (newTopology circuit) = topology circuit) :
    ConcreteAdaptivePrivacy (Aux := Aux) (scheme.mapLabels pack unpack) newTopology
      (simulator.mapLabels pack restore) randomTape realOracle idealOracle bits := by
  intro adversary circuit auxiliary parameter
  let original : AdaptiveAdversary oracle Input Public Labels Aux :=
    ⟨adversary.State, adversary.firstQueryBudget, adversary.secondQueryBudget,
      adversary.chooseInput, fun parameter circuit labels => adversary.decide parameter circuit (pack labels)⟩
  simpa only [realGame, idealGame, GarbledCircuit.mapLabels, Simulator.mapLabels, same, PMF.bind_map, Function.comp_def, adversaryWork, original]
    using privacy original circuit auxiliary parameter

namespace SimulatorProtocol

open BN254

def bits (width value : Nat) : List Bool :=
  (List.finRange width).map (BitVec.ofNat width value).getLsb

def natural (value : Nat) : List Bool :=
  List.replicate value.size true ++ false :: bits value.size value

def affine (input : AffineInput) : List Bool := bits 254 input.x.val ++ bits 254 input.y.val

def output [FieldCertificate] : Option Point → List Bool
  | none => [false, false]
  | some .zero => [false, true]
  | some (.some (x := x) (y := y) _) => [true, false] ++ affine ⟨x, y⟩

/-- The protocol fixes every query tag and every operand width. -/
noncomputable def query {FixedIndex EncIndex : Type} [Fintype FixedIndex] [Fintype EncIndex] :
    PublicQuery FixedIndex EncIndex → List Bool
  | .fixedForward index value => bits 3 0 ++ bits (Fintype.card FixedIndex).size
      (Fintype.equivFin FixedIndex index).val ++ bits 128 value.toNat
  | .fixedInverse index value => bits 3 1 ++ bits (Fintype.card FixedIndex).size
      (Fintype.equivFin FixedIndex index).val ++ bits 128 value.toNat
  | .encForward index value => bits 3 2 ++ bits (Fintype.card EncIndex).size
      (Fintype.equivFin EncIndex index).val ++ bits 128 value.toNat
  | .encInverse index value => bits 3 3 ++ bits (Fintype.card EncIndex).size
      (Fintype.equivFin EncIndex index).val ++ bits 128 value.toNat
  | .hash value => bits 3 4 ++ bits 254 value.val

/-- The parser accepts exactly the required number of little-endian bits. -/
def words (width count : Nat) (wire : List Bool) : Option (Vector (BitVec width) count) :=
  if wire.length = width * count then
    some (Vector.ofFn fun i => BitVec.ofNat width
      (((wire.drop (i.val * width)).take width).foldr (fun bit acc => bit.toNat + 2 * acc) 0))
  else none

def answer {FixedIndex EncIndex : Type} (request : PublicQuery FixedIndex EncIndex)
    (wire : List Bool) : Option request.Answer :=
  match request with
  | .fixedForward _ _ | .fixedInverse _ _ | .encForward _ _ | .encInverse _ _ =>
      (words 128 1 wire).map fun values => values[0]
  | .hash _ => (words 128 2 wire).map fun values => (values[0], values[1])

/-- The adversary keeps its original query budget. Only the simulator pays machine costs. -/
noncomputable def runProgram [BN254.FieldCertificate] {FixedIndex EncIndex Result : Type}
    [Fintype FixedIndex] [Fintype EncIndex] (machine : BoundedMachine.Machine) :
    {budget : Nat} → OracleProgram (publicOracleSpec FixedIndex EncIndex) Result budget →
      BoundedMachine.State → OptionT PMF (Result × BoundedMachine.State)
  | _, .pure distribution, state => do
      let value ← liftM distribution
      pure (value, state)
  | _, .sample distribution next, state => do
      let value ← liftM distribution
      runProgram machine (next value) state
  | _, .query request next, state => do
      let (wire, updated) ← OptionT.mk (BoundedMachine.respond machine
        ([true, false] ++ query request) { state with queries := state.queries + 1 })
      let value ← OptionT.mk (PMF.pure (answer request wire))
      runProgram machine (next value) updated

/-- The decoder supplies only the adversary's public view.
The canonical check requires the machine to produce the complete public bytes. -/
def publicValue {Public : Type} (encoding : Encoding Public) (bytes : Nat)
    (wire : List Bool) : Option Public := do
  let values ← words 8 bytes wire
  let raw := (values.map BitVec.toFin).toList
  let (value, tail) ← encoding.decode raw
  if tail.isEmpty && encoding.encode value == raw then some value else none

/-- The simulator receives no scalar. Every failed request aborts the ideal experiment. -/
noncomputable def idealGame [FieldCertificate]
    {FixedIndex EncIndex Randomness Public Key Oracle Aux : Type}
    [Fintype FixedIndex] [Fintype EncIndex]
    (scheme : GarbledCircuit NonZeroScalar AffineInput (Option Point) Randomness Public
      Key LamportSignature Oracle) (encoding : Encoding Public) (bytes : Nat)
    (machine : BoundedMachine.Machine)
    (adversary : AdaptiveAdversary (publicOracleSpec FixedIndex EncIndex)
      AffineInput Public LamportSignature Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) : PMF Bool :=
  let experiment : OptionT PMF Bool := do
    let (wire, initial) ← OptionT.mk (BoundedMachine.respond machine
      ([false, false] ++ natural parameter ++ natural bytes) (BoundedMachine.initial machine))
    let circuit ← OptionT.mk (PMF.pure (publicValue encoding bytes wire))
    let (selected, chosen) ← runProgram machine (adversary.chooseInput parameter circuit auxiliary) initial
    let (wire, encoded) ← OptionT.mk (BoundedMachine.respond machine
      ([false, true] ++ affine selected.1 ++ output (scheme.function scalar selected.1)) chosen)
    let labels ← OptionT.mk (PMF.pure (words 128 508 wire))
    let (decision, _) ← runProgram machine
      (adversary.decide parameter circuit labels auxiliary selected.2) encoded
    pure decision
  experiment.run.map (fun result => result.getD false)

end SimulatorProtocol

open BN254

/-- Adaptive privacy includes the machine budget and every implementation error.
One simulator and one machine serve every adversary and scalar. -/
def AdaptivePrivacy [FieldCertificate]
    {FixedIndex EncIndex Randomness Public Key Oracle State Aux : Type}
    [Fintype FixedIndex] [Fintype EncIndex]
    (scheme : GarbledCircuit NonZeroScalar AffineInput (Option Point) Randomness Public
      Key LamportSignature Oracle) (encoding : Encoding Public) (bytes : Nat)
    (randomTape : Nat → PMF Randomness)
    (realOracle : OracleHandler (publicOracleSpec FixedIndex EncIndex) Randomness)
    (idealOracle : OracleHandler (publicOracleSpec FixedIndex EncIndex) State)
    (idealView : State → PublicOracle FixedIndex EncIndex) : Prop :=
  ∃ simulator : Simulator AffineInput (Option Point) Public LamportSignature Nat State,
  ∃ machine : BoundedMachine.Machine,
    OracleSimulation simulator idealOracle idealView ∧
    ∀ adversary : AdaptiveAdversary (publicOracleSpec FixedIndex EncIndex)
        AffineInput Public LamportSignature Aux,
      ∀ parameter scalar auxiliary,
        let real := realGame scheme randomTape realOracle adversary parameter scalar auxiliary
        let ideal := idealGame scheme (fun _ => bytes) simulator idealOracle adversary parameter scalar auxiliary
        WorkPerAdvantage 100 (adversaryWork adversary parameter)
          (advantage real ideal + advantage ideal
            (SimulatorProtocol.idealGame scheme encoding bytes machine adversary parameter scalar auxiliary))

/-- The shared allowance bounds the real experiment against the bounded machine. -/
theorem adaptivePrivacyTransfer {real ideal bounded : PMF Bool} {work : Nat}
    (bound : WorkPerAdvantage 100 work (advantage real ideal + advantage ideal bounded)) :
    WorkPerAdvantage 100 work (advantage real bounded) :=
  le_trans (mul_le_mul_of_nonneg_right (advantageTriangle real ideal bounded) (by positivity)) bound

end Kriterion.GarbledCircuit
