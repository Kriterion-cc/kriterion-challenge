"""This test checks the local ArgoMAC baseline against the challenge library."""

from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]


def main():
    baseline = re.search(r"^baseline:\n  path: (\S+)$", (ROOT / "challenge.yaml").read_text(), re.M)
    if baseline is None:
        raise SystemExit("The challenge must select a local baseline path.")
    entry = (ROOT.parent / baseline.group(1)).resolve()
    for command in (
        ["lake", "update"],
        ["lake", "build", "Construction", "Proof"],
        ["lake", "env", "lean", "tests/ProofAudit.lean"],
        ["lake", "build", "Submission", "BaselineTests"],
        ["lake", "env", "lean", "tests/AxiomAudit.lean"],
    ):
        subprocess.run(command, cwd=entry, check=True)
    print("The local ArgoMAC baseline satisfies the Kriterion.Solution obligation.")


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as error:
        raise SystemExit(error.returncode) from error
