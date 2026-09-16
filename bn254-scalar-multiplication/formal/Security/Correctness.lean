import GarbledCircuit

/-!
This module defines perfect correctness.
The [BaBe source](https://github.com/babylonlabs-io/BaBe.latex/blob/e2dcf4d540b2708e13cd21090df759051119a116/Latex/preliminaries.tex) fixes the paper references below.
-/

namespace Kriterion.GarbledCircuit

universe uCircuit uInput uOutput uRandomness uPublic uKey uLabels uOracle

/-- Correctness specializes `preliminaries.tex`, `def:garbling-scheme`.
The challenge requires the equation for every tape and input.
When `Output` is `Option Point`, `some none` means valid evaluation that rejects an input.
The outer `none` denotes evaluation failure and cannot satisfy this equation. -/
def PerfectCorrectness
    {Circuit : Type uCircuit}
    {Input : Type uInput}
    {Output : Type uOutput}
    {Randomness : Type uRandomness}
    {Public : Type uPublic}
    {EncodingKey : Type uKey}
    {Labels : Type uLabels} {Oracle : Type uOracle}
    (scheme : GarbledCircuit Circuit Input Output Randomness Public EncodingKey Labels Oracle)
    (oracle : Randomness → Oracle) : Prop :=
  ∀ securityParameter circuit randomness input,
    let result := scheme.garble securityParameter circuit randomness
    scheme.evaluate (oracle randomness) result.1 input (scheme.encode result.2 input) =
      some (scheme.function circuit input)

end Kriterion.GarbledCircuit
