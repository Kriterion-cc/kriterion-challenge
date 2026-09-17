"""This test checks the pinned baseline against the local challenge library."""

import json
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
ENTRY = ROOT / ".lake" / "baseline-check"


def run(*args, cwd=ENTRY):
    subprocess.run(args, cwd=cwd, check=True)


def main():
    statement = (ROOT / "challenge.yaml").read_text()
    pin = re.search(r'^baseline:\n  repo: (\S+)\n  commit: "([0-9a-f]{40})"$', statement, re.M)
    if pin is None:
        raise SystemExit("The challenge has no valid baseline pin.")
    repo, commit = pin.groups()
    if not ENTRY.exists():
        run("git", "clone", "--no-checkout", repo, str(ENTRY), cwd=ROOT)
    elif (ENTRY / ".git" / "index").exists():
        run("git", "diff", "--exit-code", "--quiet", "HEAD")
    available = subprocess.run(["git", "cat-file", "-e", commit], cwd=ENTRY,
                               stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    if available.returncode != 0:
        run("git", "fetch", "--depth", "1", repo, commit)
    run("git", "checkout", "--detach", commit)
    config = f'''name = "baseline-check"
version = "0.1.0"
defaultTargets = ["Construction", "Proof", "Submission"]

[[require]]
name = "bn254-scalar-multiplication"
path = {json.dumps(str(ROOT))}

[[lean_lib]]
name = "Construction"

[[lean_lib]]
name = "Proof"

[[lean_lib]]
name = "Submission"
'''
    (ENTRY / "lakefile.toml").write_text(config)
    (ENTRY / "lean-toolchain").write_text((ROOT / "lean-toolchain").read_text())
    packages = ENTRY / ".lake" / "packages"
    packages.mkdir(parents=True, exist_ok=True)
    for package in (ROOT / ".lake" / "packages").iterdir():
        target = packages / package.name
        if package.is_dir() and not target.exists():
            target.symlink_to(package, target_is_directory=True)
    audit = '''import Submission
import Lean

example : Kriterion.Solution := Submission.solution

run_cmd do
  let illegal := (← Lean.collectAxioms `Submission.solution).filter fun name =>
    !#[`propext, `Classical.choice, `Quot.sound].contains name
  unless illegal.isEmpty do
    Lean.throwError m!"The baseline uses disallowed axioms: {illegal}"
'''
    (ENTRY / "BaselineAudit.lean").write_text(audit)
    run("lake", "update")
    run("lake", "build", "Construction", "Proof", "Submission")
    run("lake", "env", "lean", "BaselineAudit.lean")
    print(f"The baseline {commit} satisfies the local Kriterion.Solution obligation.")


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as error:
        raise SystemExit(error.returncode) from error
