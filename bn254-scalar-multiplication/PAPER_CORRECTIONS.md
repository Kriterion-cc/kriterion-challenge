# Paper corrections

This note uses BaBe.latex commit `e2dcf4d540b2708e13cd21090df759051119a116`.
The construction must use 92 digits and three shared permutation slots.
These parameters do not fix the coordinate errors below.

## Base-7 coefficients

The [base-7 appendix](https://github.com/babylonlabs-io/BaBe.latex/blob/e2dcf4d540b2708e13cd21090df759051119a116/Latex/gc_argomac_base7.tex)
conflicts with the [main text](https://github.com/babylonlabs-io/BaBe.latex/blob/e2dcf4d540b2708e13cd21090df759051119a116/Latex/gc_argomac_new.tex).
The appendix needs these corrections:

- The Y coefficient `c₂` must use `−y(K)² − 3B`.
- The Y coefficient `c₄` must include the factor `3`.
- The Z constant must use `−a x(K)` for a nonzero digit.
- The Z constant must use `a` for the zero digit.
- Both modifiers must equal zero for the zero digit.

These changes recover the main-text formulas when the digit equals one.
The tests use scale `a = 1` and mask point `K = (1, 2)`.
The input has `x = 2` and
`y = 16059845205665218889595687631975406613746683471807856151558479858750240882195`.
Lean proves that this input lies on BN254.
Lean also proves that the literal appendix output fails the Jacobian curve equation.
The main-text output satisfies that equation for this input.

## Equal points

The [preliminaries](https://github.com/babylonlabs-io/BaBe.latex/blob/e2dcf4d540b2708e13cd21090df759051119a116/Latex/preliminaries.tex)
exclude input points that equal the mask point or its negative.
The challenge requires correctness for every input and every tape.
Random mask selection does not prove that exclusion.

Lean proves that the main-text formula returns `(0, 0, 0)` when the digit
and scale equal one and both points equal `(1, 2)`.
The zero triple is not a valid Jacobian representative.
The construction therefore needs a complete addition formula.
The existing ArgoMAC construction uses complete homogeneous formulas.
Those formulas require 13 point-adaptor families.
The paper must update its formula, coordinate convention, and adaptor count
if the corrected construction retains these formulas.
The 92-digit count and the three shared permutation slots remain required.

## Regression checks

`tests/PaperFormulaChecks.lean` contains the counterexamples.
`lake build Kriterion Tests` checks these proofs and their axioms.
These checks do not prove that the complete ArgoMAC submission passes.
The bounded simulator and its instruction-cost proof remain separate obligations.
