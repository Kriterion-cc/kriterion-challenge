# BN254 scalar multiplication

This challenge ranks verified garbled-circuit constructions by their ciphertext size in bytes.

The `formal/` directory defines `Kriterion.Solution` and all fixed proof rules.
The `challenge.yaml` file contains the complete challenge definition.
The `starter/` directory contains the required submission layout.

The repository contains the complete [ArgoMAC baseline](argomac-lean/README.md).
Its [proof map](argomac-lean/Proof/README.md) describes the proof structure.
The local baseline uses the local challenge library.
Its [source record](argomac-lean/UPSTREAM.md) identifies the original repository.

## Simulator budget

The local obligation requires a finite probabilistic arithmetic machine.
Its budget is `B(q) = 10q² + 18,378,485q + 8,681,426,770,681` instructions.
Here `q` counts the oracle queries that the adversary has made.
The interpreter uses one counter for setup, both stages, and all oracle responses.
The counter includes the control table and each fair random bit.
The machine starts with zero registers, zero RAM, and empty binary stacks.
The machine has no external function calls.

The budget uses the baseline's `SimulatorTotalImplementation.resources` formula:

```text
n = q + 905765
draws = 907731 + n
B(q) = 53997367 + n*(10*n + 16) + 4*draws*(257*256) + draws
```

Lean proves the expanded formula in `BoundedMachine.budget_expanded`.
The baseline counts higher-level operations.
The formula remains a draft limit.
The arithmetic instruction set removes the need for a bit-level compiler.
The baseline defines a fixed arithmetic program.
Its complete simulation proof and total cost proof remain open.
Its existing proof does not establish this machine bound.
Authors must prove compliance with the new model.
This budget specifies instructions, not processor time or Turing-machine steps.

The machine has sixteen 256-bit registers and RAM with 256-bit addresses.
The machine also has four binary stacks for its bit protocol.
Each instruction costs one unit.
The fixed instructions support these operations:

- The word instructions perform arithmetic modulo `2^256`, bit operations, shifts, and comparison.
- The field instructions perform addition, subtraction, multiplication, and inversion in either BN254 field.
- The group instruction adds two BN254 points. It rejects invalid point encodings.
- The memory instructions read or write one RAM word. The constant instruction writes one register.
- The control instructions branch or halt.
- The stack instructions push or pop one bit. The coin instruction samples one fair bit.

The program counter has at most 256 bits.
Each control-table entry costs one unit before execution.
Each entry contains a fixed number of bounded operands.
The instruction set contains no arbitrary function or distribution values.
Each request starts at instruction zero.
Stack zero receives the request.
Stack three returns the response.
The registers, RAM, and stacks one and two retain private state between requests.
[AdaptivePrivacy.lean](formal/Security/AdaptivePrivacy.lean) fixes the request tags and bit order.
The protocol passes only public data, the selected input, and its output.

The interpreter aborts on budget exhaustion or an incorrect reply length.
The privacy proof gives one allowance to both simulation error and implementation error.
The allowance is `(Q + 1) / 2^100`.
Here `Q` is the sum of the adversary's two declared query budgets.
The adversary's local computation remains unrestricted.
`adaptivePrivacyTransfer` proves the resulting real-to-machine bound.

The revision retains the existing circuit types and byte encoding.
The machine must produce the complete canonical public bytes.
The decoder supplies only the adversary's public view.
The machine never receives the decoded value.
The protocol represents each finite oracle index by its fixed enumeration.
The single `AdaptivePrivacy` property requires both the abstract simulator and its bounded machine.
The older `ConcreteAdaptivePrivacy` predicate remains an abstract game bound for proof reuse.
`Solution` checks only the combined `AdaptivePrivacy` property.
Old submissions need a new bounded simulator proof.

The library and starter pins still select the previous published obligation.
The publisher must update both pins before deployment.

## Build the public library

Install `elan`, and then run these commands:

```sh
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
The local baseline currently fails the revised obligation.
This revision is not ready for deployment.

## Start a submission

Copy the contents of `starter/` into a new public Git repository.
Replace the placeholder in `Submission.lean` with a complete `Kriterion.Solution` value.

The starter follows the baseline's four proof roots: correctness, privacy,
Lamport compatibility, and ciphertext size. You can change the internal module
layout if `Proof.lean` exports all results needed by `Submission.solution`.

Run these commands in the new repository:

```sh
lake update
lake exe cache get
lake build
```

The local build accepts the starter placeholder with a warning.
The Kriterion verifier rejects the placeholder and all other unproved axioms.

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
It then evaluates `Kriterion.Benchmark.ciphertextBytes` for the submitted solution.
