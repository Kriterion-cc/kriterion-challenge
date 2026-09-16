import Cryptography.Primitives

/-!
This module defines garbling and Lamport interfaces.
The [BaBe source](https://github.com/babylonlabs-io/BaBe.latex/blob/e2dcf4d540b2708e13cd21090df759051119a116/Latex/preliminaries.tex) fixes the paper references below.
-/

namespace Kriterion

universe uCircuit uInput uOutput uRandomness uPublic uKey uLabels uOracle uTopology uState

/-- A garbled circuit has separate garbling, encoding, and evaluation steps. -/
structure GarbledCircuit
    (Circuit : Type uCircuit)
    (Input : Type uInput)
    (Output : Type uOutput)
    (Randomness : Type uRandomness)
    (Public : Type uPublic)
    (EncodingKey : Type uKey)
    (Labels : Type uLabels) (Oracle : Type uOracle) where
  /-- The target is the circuit function in `preliminaries.tex`, `def:garbling-scheme`. -/
  function : Circuit → Input → Output
  /-- `Garble` returns the public ciphertext and private key in `def:garbling-scheme`. -/
  garble : Nat → Circuit → Randomness → Public × EncodingKey
  /-- `Encode` selects the input labels in `def:garbling-scheme`. -/
  encode : EncodingKey → Input → Labels
  /-- The evaluator knows its input. This explicit argument is a challenge convention. -/
  evaluate : Oracle → Public → Input → Labels → Option Output

namespace GarbledCircuit

/-- This adapter changes the wire labels without changing the target or public circuit. -/
def mapLabels (scheme : GarbledCircuit Circuit Input Output Randomness Public Key Labels Oracle)
    (pack : Labels → Wire) (unpack : Input → Wire → Labels) :
    GarbledCircuit Circuit Input Output Randomness Public Key Wire Oracle where
  function := scheme.function
  garble := scheme.garble
  encode key input := pack (scheme.encode key input)
  evaluate oracle circuit input labels := scheme.evaluate oracle circuit input (unpack input labels)

/-- A Bitcoin hash is the 160-bit output used by the paper's hash locks. -/
abbrev BitcoinHash := BitVec 160
abbrev LamportSecretKey := Vector (Cryptography.Block × Cryptography.Block) 508
abbrev LamportPublicKey := Vector (BitcoinHash × BitcoinHash) 508
abbrev LamportSignature := Vector Cryptography.Block 508

/-- Hash locks implement `preliminaries.tex`, `eq:lampsig-pk`. The hash is an explicit parameter. -/
def lamportPublicKey (hashBTC : Cryptography.Block → BitcoinHash)
    (key : LamportSecretKey) : LamportPublicKey :=
  Vector.ofFn fun index => (hashBTC (key[index]).1, hashBTC (key[index]).2)

/-- Encoding selects each message-bit label in `preliminaries.tex`, `eq:lampsig-sig`. -/
def selectLamportLabels (pairs : LamportSecretKey)
    (bits : BitVec 508) : Vector Cryptography.Block 508 :=
  Vector.ofFn fun index => if bits.getLsb index then (pairs[index]).2 else (pairs[index]).1

/-- This is Equation `eq:lampsig-verify` from the BaBe paper source. -/
def LamportVerify (hashBTC : Cryptography.Block → BitcoinHash) (key : LamportPublicKey)
    (message : BitVec 508) (signature : LamportSignature) : Prop :=
  ∀ index, hashBTC signature[index] =
    if message.getLsb index then (key[index]).2 else (key[index]).1

/-- The encoding key is a Lamport key for the fixed input-bit representation. -/
structure LamportCompatibility
    {Circuit : Type uCircuit} {Input : Type uInput} {Output : Type uOutput}
    {Randomness : Type uRandomness} {Public : Type uPublic}
    {EncodingKey : Type uKey} {Oracle : Type uOracle}
    (scheme : GarbledCircuit Circuit Input Output Randomness Public EncodingKey LamportSignature Oracle)
    (inputBits : Input → BitVec 508) where
  /-- The 508 pairs follow `gc_argomac.tex`, Step 3, in x-then-y order. -/
  keyPairs : EncodingKey → Vector (Cryptography.Block × Cryptography.Block) 508
  /-- Equality excludes extra payloads. This requirement strengthens a projection-only check. -/
  encodeSelectsLabels : ∀ key input,
    scheme.encode key input = selectLamportLabels (keyPairs key) (inputBits input)

/-- Compatible encoded labels satisfy the Bitcoin Lamport hash locks. -/
theorem LamportCompatibility.encodeVerifies
    {Circuit : Type uCircuit} {Input : Type uInput} {Output : Type uOutput}
    {Randomness : Type uRandomness} {Public : Type uPublic}
    {EncodingKey : Type uKey} {Oracle : Type uOracle}
    {scheme : GarbledCircuit Circuit Input Output Randomness Public EncodingKey LamportSignature Oracle}
    {inputBits : Input → BitVec 508} (compatible : LamportCompatibility scheme inputBits)
    (hashBTC : Cryptography.Block → BitcoinHash) (key : EncodingKey) (input : Input) :
    LamportVerify hashBTC (lamportPublicKey hashBTC (compatible.keyPairs key))
      (inputBits input) (scheme.encode key input) := by
  intro index
  rw [compatible.encodeSelectsLabels]
  simp [lamportPublicKey, selectLamportLabels]
  split <;> rfl

/-- A simulator uses private coins, the circuit topology, and the selected output. -/
structure Simulator
    (Input : Type uInput)
    (Output : Type uOutput)
    (Public : Type uPublic)
    (Labels : Type uLabels)
    (Topology : Type uTopology)
    (State : Type uState) where
  /-- `Sim₁` receives topology before the input choice in `def:garbling-scheme`. -/
  simulateGarble : Nat → Topology → PMF (Public × State)
  /-- `Sim₂` receives the chosen input and its output in `def:garbling-scheme`. -/
  simulateEncode : State → Input → Output → PMF (Labels × State)

/-- A public adapter changes label and topology representations without adding information. -/
noncomputable def Simulator.mapLabels (simulator : Simulator Input Output Public Labels Topology State)
    (pack : Labels → Wire) (restore : NewTopology → Topology) :
    Simulator Input Output Public Wire NewTopology State :=
  ⟨fun parameter value => simulator.simulateGarble parameter (restore value),
    fun state input output => (simulator.simulateEncode state input output).map
      (fun result => (pack result.1, result.2))⟩

end GarbledCircuit

end Kriterion
