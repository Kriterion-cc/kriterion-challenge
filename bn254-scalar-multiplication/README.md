# BN254 scalar multiplication

This challenge ranks verified garbled-circuit constructions by their ciphertext size in bytes.

The `formal/` directory defines `Kriterion.Solution` and all fixed proof rules.
The `challenge.yaml` file contains the complete challenge definition.
The `argomac-lean/` directory contains the complete ArgoMAC construction, proofs, and tests.

The repository contains the complete [ArgoMAC baseline](argomac-lean/README.md).
Its [proof map](argomac-lean/Proof/README.md) describes the proof structure.
The baseline submodule pins `Kriterion-cc/argomac-lean`.
The local test overrides its Git dependency with the local challenge library.
Its [source record](argomac-lean/UPSTREAM.md) identifies the original repository.

## Problem and rules

The `statement` field in [challenge.yaml](challenge.yaml) states the complete problem.
It defines the target function, Lamport labels, correctness equation, privacy experiments,
simulator machine, public encoding, score, and verification rules.
The `references` field links each formal requirement to its pinned source.
The statement keeps the field and group certificate premises explicit.

The real and ideal games share one fixed lazy oracle.
The oracle serves public queries directly.
The simulator can read existing mappings and program fresh mappings.
The simulator uses one closed instruction table.
The table and both stage limits must sum to at most `2^60`.
The adversary pays for its table, both stage limits, and its decision allowance.

The garbling program uses at most 1,759,967 public queries.
The evaluation program uses at most 1,055,879 public queries.
These limits are acceptance gates.
Only ciphertext bytes determine the rank.
The BN254 axiom list stays empty until a cryptographic review sets concrete bounds.

## Build the public library

Install `elan`, and then run these commands:

```sh
git submodule update --init --recursive
cd bn254-scalar-multiplication
lake exe cache get
lake build Kriterion Tests
lake test
```

The project uses Lean 4.33.1, Mathlib 4.33.1, and a pinned VCV-io revision.
The `lake test` command also checks the ArgoMAC baseline in `argomac-lean/`.
The test uses the local library and checks `Submission.solution` for disallowed axioms.
The test also compiles the baseline acceptance tests in `tests/AdaptivePrivacy.lean`.
The test requires Python 3.
The first dependency download requires network access.
The baseline must pass this test before deployment.
`Submission.solution` supplies the complete bounded simulator proof.

## Start a submission

Use `argomac-lean/` as the source for a new submission.
The starter contains the ArgoMAC implementation.
Its adaptive privacy proof includes the complete arithmetic simulator.
The Lake configuration pins the public challenge library.
A separate submission repository uses the same configuration.

The starter follows the baseline's four proof roots: correctness, privacy,
Lamport compatibility, and ciphertext size. You can change the internal module
layout if `Proof.lean` exports all results needed by `Submission.solution`.

Run these commands in the new repository:

```sh
lake update
lake exe cache get
lake build
```

The starter proves every field of `Kriterion.Solution`.
The Kriterion verifier rejects incomplete proofs and disallowed axioms.

Before submission, push the repository and use its full 40-character commit hash.

## Submit to Kriterion

Choose one of these public resources:

- [Download the CLI and verify its checksum](https://kriterion.cc/download)
- [Read the first-submission guide](https://kriterion.cc/docs/tutorials/first-submission)
- [Inspect the CLI source and past releases](https://github.com/Kriterion-cc/kriterion-cli)

Set `KRITERION_TOKEN`.
The token is available from the Settings page on `https://kriterion.cc`.

```sh
curl -fsSL https://raw.githubusercontent.com/Kriterion-cc/kriterion-cli/v0.1.0/kriterion -o kriterion
chmod +x kriterion
export KRITERION_TOKEN='<token-from-settings>'
REPO_URL='https://github.com/you/project'
COMMIT=$(git rev-parse HEAD)
./kriterion submit \
  --challenge scalar-multiplication \
  --repo "$REPO_URL" \
  --commit "$COMMIT"
```

The hosted verifier runs the final layout, build, obligation, axiom, and computability checks.

## Verification rules

The verifier imports only `Construction`, `Proof`, and `Submission` from the submitted repository.
It gets this formal library from the exact public commit in `challenge.yaml`.

The verifier checks the layout, Lean build, obligation, axioms, and executable construction.
It then evaluates the ciphertext size and both construction query bounds.
