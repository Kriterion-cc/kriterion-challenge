# BN254 scalar multiplication

This challenge ranks verified garbled-circuit constructions by their ciphertext size in bytes.

The `formal/` directory defines `Kriterion.Solution` and all fixed proof rules.
The `challenge.yaml` file contains the complete challenge definition.
The `starter/` directory contains the required submission layout.

The public baseline is [ArgoMAC](https://github.com/SebastianElvis/argomac-lean).
Kriterion uses commit `711689cd0253edece8d0c617ad5a7afaa937673e` for that baseline.

## Build the public library

Install `elan`, and then run these commands:

```sh
cd bn254-scalar-multiplication
lake exe cache get
lake build Kriterion Tests
```

The project uses Lean 4.33.1, Mathlib 4.33.1, and a pinned VCV-io revision.

## Start a submission

Copy the contents of `starter/` into a new public Git repository.
Replace the placeholder in `Submission.lean` with a complete `Kriterion.Solution` value.

Run these commands in the new repository:

```sh
lake update
lake exe cache get
lake build
```

The local build accepts the starter placeholder with a warning.
The Kriterion verifier rejects the placeholder and all other unproved axioms.

Before submission, push the repository and use its full 40-character commit hash.

## Verification rules

The verifier imports only `Construction`, `Proof`, and `Submission` from the submitted repository.
It gets this formal library from the exact public commit in `challenge.yaml`.

The verifier checks the layout, Lean build, obligation, axioms, and executable construction.
It then evaluates `Kriterion.Benchmark.ciphertextBytes` for the submitted solution.

