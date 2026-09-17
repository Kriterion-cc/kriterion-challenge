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
