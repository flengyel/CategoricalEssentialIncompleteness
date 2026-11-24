import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess


here = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description="Replay both encoded-language Visser proofs on the tested checkout.")
parser.add_argument("--project", type=Path, default=here.parent / "cei-v81-final", help="Root of the tested Lean project checkout")
project = parser.parse_args().project.resolve()
lean_root = project / "Lean"
source = subprocess.check_output(["git", "-C", str(project), "rev-parse", "HEAD"], text=True).strip()
toolchain = (lean_root / "lean-toolchain").read_text().strip()
manifest = json.loads((lean_root / "lake-manifest.json").read_text())
dependencies = {p["name"]: p["rev"] for p in manifest["packages"] if p["name"] in {"Foundation", "mathlib"}}
libraries = [lean_root / ".lake/build/lib/lean", *sorted((lean_root / ".lake/packages").glob("*/.lake/build/lib/lean"))]
lean_env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, libraries)))

for receipt_name in ["visser-reduction-receipt.json", "visser-theorem-extension-receipt.json"]:
    receipt = json.loads((here / receipt_name).read_text())
    test = here / receipt["test"]
    digest = hashlib.sha256(test.read_bytes()).hexdigest()
    if (source, toolchain, dependencies, digest) != (receipt["source"], receipt["toolchain"], receipt["dependencyRevisions"], receipt["sha256"]):
        raise SystemExit(f"Input mismatch for {test.name}")
    run = subprocess.run(["elan", "run", toolchain, "lean", "-j1", "-M3100", test.name], cwd=here, env=lean_env, capture_output=True, text=True, timeout=120)
    if run.returncode != 0 or run.stdout + run.stderr != receipt["stdoutAndStderr"]:
        raise SystemExit(f"Lean replay differs for {test.name}\n{run.stdout}{run.stderr}")
    print(f"{test.name} verified at {source}")
