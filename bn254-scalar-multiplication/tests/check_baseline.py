"""This test checks the local ArgoMAC baseline against the challenge library."""

from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
ENTRY = ROOT / "argomac-lean"


def main():
    for command in (
        ["lake", "update"],
        ["lake", "build", "Construction", "Proof", "Submission", "BaselineTests"],
        ["lake", "env", "lean", "tests/AxiomAudit.lean"],
    ):
        subprocess.run(command, cwd=ENTRY, check=True)
    print("The local ArgoMAC baseline satisfies the Kriterion.Solution obligation.")


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as error:
        raise SystemExit(error.returncode) from error
