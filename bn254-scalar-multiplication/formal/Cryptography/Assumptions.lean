import Cryptography.Primitives

/-!
This module defines the challenge security bounds.
The [BaBe source](https://github.com/babylonlabs-io/BaBe.latex/blob/e2dcf4d540b2708e13cd21090df759051119a116/Latex/gc_rpm_proof.tex) fixes the paper references below.
-/

namespace Kriterion.Cryptography.Assumptions

open Cryptography

/-- This value is the difference between two acceptance probabilities. -/
noncomputable def advantage (first second : PMF Bool) : ℝ :=
  |(first true).toReal - (second true).toReal|

/-- The challenge requires `advantage ≤ work / 2^bits`. This convention fixes concrete security. -/
def WorkPerAdvantage (bits work : Nat) (error : ℝ) : Prop :=
  error * (2 : ℝ) ^ bits ≤ work

/-- This condition applies one concrete bound to every query budget. -/
def ConcreteBound (bits : Nat) (work : Nat → Nat) (error : Nat → ℝ) : Prop :=
  ∀ queries, WorkPerAdvantage bits (work queries) (error queries)

theorem concreteBoundAdd {bits : Nat} {firstWork secondWork : Nat → Nat}
    {firstError secondError : Nat → ℝ}
    (first : ConcreteBound bits firstWork firstError)
    (second : ConcreteBound bits secondWork secondError) :
    ConcreteBound bits (fun queries => firstWork queries + secondWork queries)
      (fun queries => firstError queries + secondError queries) := by
  intro queries
  rw [WorkPerAdvantage, add_mul, Nat.cast_add]
  exact add_le_add (first queries) (second queries)

theorem advantageTriangle (first middle last : PMF Bool) :
    advantage first last ≤ advantage first middle + advantage middle last := by
  unfold advantage
  rw [show (first true).toReal - (last true).toReal =
    ((first true).toReal - (middle true).toReal) +
      ((middle true).toReal - (last true).toReal) by ring]
  exact abs_add_le _ _

/-- This certificate fixes the joint law of the public ideal oracles.
The BaBe permutation model appears in `preliminaries.tex`, `def:pRPM`.
The hash uses an independent uniform function. Encryption reductions must use this fixed model.
BN254 arithmetic premises remain explicit in `Solution.scheme`. This certificate adds no IND-CPA axiom.
The certificate permits no caller-defined advantage or work function. -/
def StandardAssumptions (FixedIndex EncIndex Tape : Type)
    [Fintype FixedIndex] [Fintype EncIndex] [Fintype Tape]
    (witness : Tape) (project : Tape → PublicOracle FixedIndex EncIndex) : Prop :=
  (uniformTape Tape witness).map project = PMF.uniformOfFintype (PublicOracle FixedIndex EncIndex)

end Kriterion.Cryptography.Assumptions
