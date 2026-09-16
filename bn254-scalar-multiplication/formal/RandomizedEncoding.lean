import Mathlib.Logic.Equiv.Defs

/-!
This module defines uniform randomized encoding.
The [BaBe source](https://github.com/babylonlabs-io/BaBe.latex/blob/e2dcf4d540b2708e13cd21090df759051119a116/Latex/gc_argomac_new.tex) fixes the paper references below.
-/

namespace Kriterion

universe uInput uOutput uRandomness uEncoded

/-- A randomized encoding has an encoder and a decoder. -/
structure RandomizedEncoding
    (Input : Type uInput)
    (Output : Type uOutput)
    (Randomness : Type uRandomness)
    (Encoded : Type uEncoded) where
  function : Input → Output
  encode : Input → Randomness → Encoded
  decode : Encoded → Option Output

namespace RandomizedEncoding

/-- Correctness requires the decoder to recover the function output. -/
def Correctness
    {Input : Type uInput}
    {Output : Type uOutput}
    {Randomness : Type uRandomness}
    {Encoded : Type uEncoded}
    (encoding : RandomizedEncoding Input Output Randomness Encoded) : Prop :=
  ∀ input randomness,
    encoding.decode (encoding.encode input randomness) = some (encoding.function input)

/-- A simulator makes an encoding from only the function output. -/
structure Simulator
    (Output : Type uOutput) (Randomness : Type uRandomness) (Encoded : Type uEncoded) where
  simulate : Output → Randomness → Encoded

/-- `UniformEquivalent` identifies samplers through a random-tape permutation. -/
def UniformEquivalent {Randomness : Type uRandomness} {Encoded : Type uEncoded}
    (first second : Randomness → Encoded) : Prop :=
  ∃ reindex : Equiv Randomness Randomness, ∀ randomness,
    first randomness = second (reindex randomness)

/-- A tape permutation proves equality of the real and simulated uniform distributions.
This helper supports `preliminaries.tex`, `def:garbling-scheme`. The caller cannot select another relation. -/
def Privacy
    {Input : Type uInput}
    {Output : Type uOutput}
    {Randomness : Type uRandomness}
    {Encoded : Type uEncoded}
    (encoding : RandomizedEncoding Input Output Randomness Encoded)
    (simulator : Simulator Output Randomness Encoded) : Prop :=
  ∀ input,
    UniformEquivalent
      (fun randomness => encoding.encode input randomness)
      (fun randomness => simulator.simulate (encoding.function input) randomness)

end RandomizedEncoding

end Kriterion
