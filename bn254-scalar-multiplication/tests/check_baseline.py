"""This test checks the pinned ArgoMAC baseline against the local challenge library."""

import json
from pathlib import Path
import re
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[1]


def main():
    entry = ROOT / "argomac-lean"
    baseline = re.search(r"^baseline:\n  repo: (\S+)\n  commit: \"([0-9a-f]{40})\"$",
                         (ROOT / "challenge.yaml").read_text(), re.M)
    url = subprocess.check_output(["git", "config", "--file", str(ROOT.parent / ".gitmodules"),
                                   "submodule.bn254-scalar-multiplication/argomac-lean.url"], text=True).strip()
    commit = subprocess.check_output(["git", "-C", str(entry), "rev-parse", "HEAD"], text=True).strip()
    if baseline is None or baseline.groups() != (url, commit):
        raise SystemExit("The baseline must match the ArgoMAC submodule URL and commit.")
    if any((path / "lakefile.lean").exists() for path in (ROOT, entry)):
        raise SystemExit("The challenge and baseline must use their lakefile.toml files.")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    packages = [{**package, "type": "path", "dir": str(ROOT / ".lake/packages" / package["name"] /
                 (package.get("subDir") or ""))} for package in manifest["packages"]]
    packages.append({"type": "path", "name": manifest["name"], "dir": str(ROOT), "inherited": False,
                     "manifestFile": "lake-manifest.json", "configFile": "lakefile.toml"})
    with tempfile.NamedTemporaryFile(mode="w", suffix=".json") as overrides:
        json.dump({"version": manifest["version"], "packages": packages}, overrides)
        overrides.flush()
        for command in (
            ["build", "Construction", "Proof"],
            ["env", "lean", "tests/ProofAudit.lean"],
            ["build", "Submission", "BaselineTests"],
            ["env", "lean", "tests/AxiomAudit.lean"],
        ):
            subprocess.run(["lake", f"--packages={overrides.name}", *command], cwd=entry, check=True)
    print("The pinned ArgoMAC baseline satisfies the local Kriterion.Solution obligation.")


if __name__ == "__main__":
    try:
        main()
    except subprocess.CalledProcessError as error:
        raise SystemExit(error.returncode) from error
