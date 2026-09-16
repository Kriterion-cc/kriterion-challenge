import GarbledCircuit
import Cryptography.Assumptions

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

/-- The challenge bounds the advantage between the two BaBe experiments.
The work-per-advantage inequality is a concrete challenge rule, not BaBe's PPT definition. -/
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

end Kriterion.GarbledCircuit
