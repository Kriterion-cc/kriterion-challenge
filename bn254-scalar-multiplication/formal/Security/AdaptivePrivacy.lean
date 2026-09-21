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

/-- The decoder supplies only the adversary's public view.
The canonical check requires the machine to produce the complete public bytes. -/
def publicValue {Public : Type} (encoding : Encoding Public) (bytes : Nat)
    (wire : List Bool) : Option Public := do
  let values ← words 8 bytes wire
  let raw := (values.map BitVec.toFin).toList
  let (value, tail) ← encoding.decode raw
  if tail.isEmpty && encoding.encode value == raw then some value else none

end SimulatorProtocol

open BN254

/-- The shared allowance bounds the real experiment against the bounded machine. -/
theorem adaptivePrivacyTransfer {real ideal bounded : PMF Bool} {work : Nat}
    (bound : WorkPerAdvantage 100 work (advantage real ideal + advantage ideal bounded)) :
    WorkPerAdvantage 100 work (advantage real bounded) :=
  le_trans (mul_le_mul_of_nonneg_right (advantageTriangle real ideal bounded) (by positivity)) bound

/-- The machine receives public bytes and retains only its finite machine state. -/
noncomputable def machineAdversary [FieldCertificate]
    {FixedIndex EncIndex Public : Type} [Fintype FixedIndex] [Fintype EncIndex]
    (encoding : Encoding Public) (machine : BoundedMachine.Adversary) :
    AdaptiveAdversary (publicOracleSpec FixedIndex EncIndex) AffineInput Public LamportSignature Unit where
  State := Option (BoundedMachine.Configuration (machine.size + 1))
  firstQueryBudget := fun _ => machine.firstFuel
  secondQueryBudget := fun _ => machine.secondFuel
  chooseInput := fun parameter circuit _ =>
    let wire := SimulatorProtocol.natural parameter ++
      (encoding.encode circuit).flatMap (fun byte => SimulatorProtocol.bits 8 byte.val)
    let memory : BoundedMachine.Memory := { bits := fun stack => if stack = 0 then wire else [] }
    OracleProgram.map (fun result =>
        ((match result with
          | none => ⟨0, 0⟩
          | some state => ⟨(state.memory.registers 0).toNat, (state.memory.registers 1).toNat⟩), result)) (machine.program machine.firstFuel ⟨0, memory⟩)
  decide := fun _ _ labels _ state => match state with
    | none => .pure (PMF.pure false)
    | some state =>
      let wire := labels.toList.flatMap (fun label => SimulatorProtocol.bits 128 label.toNat)
      let memory := { state.memory with bits := Function.update state.memory.bits 0 wire }
      OracleProgram.map (fun result => result.any (fun final => final.memory.registers 0 == 1))
        (machine.program machine.secondFuel ⟨0, memory⟩)

/-- The real game uses independent private coins and one fixed lazy oracle. -/
noncomputable def lazyRealGame
    {FixedIndex EncIndex Coins Circuit Input Public Key Labels Aux : Type}
    [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (coins : Nat → PMF Coins) {budget : Nat}
    (garble : Nat → Circuit → Coins → OracleProgram (publicOracleSpec FixedIndex EncIndex) (Public × Key) budget)
    (encode : Key → Input → Labels)
    (adversary : AdaptiveAdversary (publicOracleSpec FixedIndex EncIndex) Input Public Labels Aux)
    (parameter : Nat) (circuit : Circuit) (auxiliary : Aux) : PMF Bool :=
  (coins parameter).bind fun randomness =>
    (LazyOracle.run (garble parameter circuit randomness) LazyOracle.empty).bind fun garbled =>
      (LazyOracle.run (adversary.chooseInput parameter garbled.1.1 auxiliary) garbled.2).bind fun selected =>
        (LazyOracle.run (adversary.decide parameter garbled.1.1
          (encode garbled.1.2 selected.1.1) auxiliary selected.1.2) selected.2).map Prod.fst

namespace LazySimulatorProtocol

/-- The fixed oracle serves all adversary queries without invoking the simulator. -/
noncomputable def idealGame [FieldCertificate]
    {FixedIndex EncIndex Randomness Public Key Oracle Aux : Type}
    [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (scheme : GarbledCircuit NonZeroScalar AffineInput (Option Point) Randomness Public
      Key LamportSignature Oracle) (encoding : Encoding Public) (bytes : Nat)
    (machine : BoundedMachine.Simulator)
    (adversary : AdaptiveAdversary (publicOracleSpec FixedIndex EncIndex)
      AffineInput Public LamportSignature Aux)
    (parameter : Nat) (scalar : NonZeroScalar) (auxiliary : Aux) : PMF Bool :=
  let experiment : OptionT PMF Bool := do
    let memory : BoundedMachine.Memory := { bits := fun stack =>
      if stack = 0 then [false, false] ++ SimulatorProtocol.natural parameter ++ SimulatorProtocol.natural bytes else [] }
    let (initial, oracle, _) ← OptionT.mk (machine.run machine.firstFuel ⟨0, memory⟩ LazyOracle.empty)
    let circuit ← OptionT.mk (PMF.pure (SimulatorProtocol.publicValue encoding bytes (initial.memory.bits 3)))
    let (selected, chosen) ← liftM (LazyOracle.run (adversary.chooseInput parameter circuit auxiliary) oracle)
    let request := [false, true] ++ SimulatorProtocol.affine selected.1 ++
      SimulatorProtocol.output (scheme.function scalar selected.1)
    let memory := { initial.memory with bits := Function.update (Function.update initial.memory.bits 0 request) 3 [] }
    let (encoded, updated, _) ← OptionT.mk (machine.run machine.secondFuel ⟨0, memory⟩ chosen)
    let labels ← OptionT.mk (PMF.pure (SimulatorProtocol.words 128 508 (encoded.memory.bits 3)))
    let (decision, _) ← liftM (LazyOracle.run
      (adversary.decide parameter circuit labels auxiliary selected.2) updated)
    pure decision
  experiment.run.map (fun result => result.getD false)

end LazySimulatorProtocol

/-- One closed simulator uses the fixed oracle under the constant shared allowance. -/
def OracleAdaptivePrivacy [FieldCertificate]
    {FixedIndex EncIndex Coins Randomness Public Key Oracle : Type}
    [Fintype FixedIndex] [Fintype EncIndex] [DecidableEq FixedIndex] [DecidableEq EncIndex]
    (scheme : GarbledCircuit NonZeroScalar AffineInput (Option Point) Randomness Public
      Key LamportSignature Oracle) (encoding : Encoding Public) (bytes : Nat)
    (coins : Nat → PMF Coins) {budget : Nat}
    (garble : Nat → NonZeroScalar → Coins →
      OracleProgram (publicOracleSpec FixedIndex EncIndex) (Public × Key) budget) : Prop :=
  ∃ simulator : BoundedMachine.Simulator, ∀ machine : BoundedMachine.Adversary,
    ∀ parameter scalar,
      let adversary := machineAdversary encoding machine
      WorkPerAdvantage 100 (machine.steps + 1)
        (advantage (lazyRealGame coins garble scheme.encode adversary parameter scalar ())
          (LazySimulatorProtocol.idealGame scheme encoding bytes simulator adversary parameter scalar ()))

end Kriterion.GarbledCircuit
