# White Hat Challenge

This public repository contains formal Kriterion challenge definitions and starter submissions.

Participants can inspect each Lean library without access to a private organization.
They can also build a starter submission locally before they submit a pinned Git commit.

## Challenges

- [BN254 scalar multiplication](bn254-scalar-multiplication/README.md)

Each challenge directory contains its statement, formal library, dependency pins, tests, and starter submission.
The BN254 challenge also contains the complete [ArgoMAC source and proofs](bn254-scalar-multiplication/argomac-lean/README.md).

## Challenge versions

The `version` field in [the challenge definition](bn254-scalar-multiplication/challenge.yaml)
names the statement and its pinned formal rules.
The repository release tag matches that version with a `v` prefix.
Use stable semantic versions without leading zeroes.

- Increase the major version for incompatible submission requirements.
- Increase the minor version for compatible extensions.
- Increase the patch version for corrections that preserve the rules.

Version `1.0.0` identifies the rules before the bounded simulator requirement.
That historical YAML has no version field. The `v1.0.0` tag identifies it.
Version `2.0.0` requires a finite arithmetic simulator and its instruction-cost proof.
It also includes implementation, sampling, and abort errors in the privacy allowance.
Existing submissions need the new privacy proof and library pin.

The earlier `v1.1.0` tag identifies the rules before the explicit version field.
Use `v2.0.0` for the release with the new field and the incompatible proof requirements.

## Participant CLI

The canonical participant CLI is in the public
[Kriterion CLI repository](https://github.com/Kriterion-cc/kriterion-cli).
It requires Node.js 18 or newer.

Choose one of these public resources:

- [Download the CLI](https://kriterion.cc/download)
- [Read the participant documentation](https://kriterion.cc/docs)
- [Inspect the CLI source](https://github.com/Kriterion-cc/kriterion-cli)

Download it and make it executable:

```sh
curl -fsSL https://raw.githubusercontent.com/Kriterion-cc/kriterion-cli/v0.1.0/kriterion -o kriterion
chmod +x kriterion
./kriterion --help
```

Set `KRITERION_TOKEN` to the token from the Kriterion Settings page.
The CLI uses `https://api.kriterion.cc` by default.
