# Starter submission

Copy all files in this directory to the root of a new public Git repository.

Keep these required files:

- `Construction.lean` contains executable construction code.
- `Proof.lean` exports the four proof roots.
- `Proof/Correctness.lean` contains correctness proofs.
- `Proof/Privacy.lean` contains adaptive privacy proofs.
- `Proof/LamportCompatibility.lean` contains Lamport label proofs.
- `Proof/CiphertextSize.lean` contains ciphertext size proofs.
- `Submission.lean` defines `Submission.solution`.
- `lakefile.toml` pins the public challenge package.
- `lean-toolchain` pins Lean.

Replace the `sorry` placeholder before submission.
The hosted verifier rejects `sorry`, axioms, opaque definitions, and noncomputable construction code.

This proof layout follows the current ArgoMAC baseline. You can add nested modules
or change the internal layout. Keep `Proof.lean` as the exported proof root.

The local challenge now requires a bounded simulator machine.
The circuit types and byte encoding remain unchanged.
Authors must supply the new privacy proof for the bounded simulator.
The current dependency pin still selects the previous published obligation.
The publisher must update this pin before authors can target the revision.

The [paper corrections](PAPER_CORRECTIONS.md) explain the coordinate errors.
