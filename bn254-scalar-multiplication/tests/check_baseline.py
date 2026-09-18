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
    if entry != ROOT / "argomac-lean":
        raise SystemExit("The baseline must use the local argomac-lean directory.")
    if any((path / "lakefile.lean").exists() for path in (ROOT, entry)):
        raise SystemExit("The challenge and baseline must use their lakefile.toml files.")
    config = "\n".join(line.split("#", 1)[0].strip()
                       for line in (entry / "lakefile.toml").read_text().splitlines())
    if re.search(r"^\[(?!\[\s*(?:require|lean_lib)\s*\]\]$)", config, re.M):
        raise SystemExit("The baseline must use only canonical require and lean_lib sections.")
    dependencies = re.findall(r"^\[\[\s*require\s*\]\]\s*\n(.*?)(?=^\[|\Z)", config, re.M | re.S)
    if len(dependencies) != 1 or not re.fullmatch(
        r'\s*name\s*=\s*"bn254-scalar-multiplication"\s+path\s*=\s*"\.\."\s*', dependencies[0]
    ):
        raise SystemExit("The baseline must require the local challenge package by path.")
    if (entry / "..").resolve() != ROOT:
        raise SystemExit("The baseline dependency must resolve to the local challenge directory.")
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
