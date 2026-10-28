#!/usr/bin/env python3
"""Build the categorical essential-incompleteness development and audit its transitive proof axioms."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "Lean"
LOGS = ROOT / "build-logs"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
AUDITED = [
    "CategoricalEssentialIncompleteness.arithmeticRecursionCategory",
    "CategoricalEssentialIncompleteness.arithmeticEvaluatorIsTuring",
    "FailureOfComposition.Palomar.obstruction_four_properties",
    "FailureOfComposition.Palomar.no_quotient_composition_productive",
    "FailureOfComposition.Palomar.no_quotient_composition_godel",
    "FailureOfComposition.Palomar.pi_one_characterization",
    "FailureOfComposition.Palomar.generated_congruence_classification",
    "FailureOfComposition.Palomar.weak_totality_counterexample",
    "FailureOfComposition.Palomar.range_counterexample_godel",
    "FailureOfComposition.Palomar.range_counterexample_productive",
    "FailureOfComposition.Palomar.generated_quotient_partial_recursive",
    "CategoricalEssentialIncompleteness.ComplementaryPair.eq_of_le",
    "CategoricalEssentialIncompleteness.DiagonalData.diagonal_collapse",
    "CategoricalEssentialIncompleteness.DiagonalData.integration_diagonal",
    "CategoricalEssentialIncompleteness.DiagonalData.inseparable",
    "CategoricalEssentialIncompleteness.domainInverseImage_meet",
    "CategoricalEssentialIncompleteness.restrictionPredicates",
    "CategoricalEssentialIncompleteness.totalBinaryProductLimit",
    "CategoricalEssentialIncompleteness.restriction_integration_diagonal",
    "CategoricalEssentialIncompleteness.restriction_inseparable",
    "CategoricalEssentialIncompleteness.parameterized_separator_factorization",
    "CategoricalEssentialIncompleteness.no_global_point_of_factorization",
    "CategoricalEssentialIncompleteness.BooleanPresentation.quotient",
    "CategoricalEssentialIncompleteness.boundFiber_le_postcomp",
    "CategoricalEssentialIncompleteness.represented_extension_incomplete",
    "CategoricalEssentialIncompleteness.boolean_quotient_incomplete",
]


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def main() -> int:
    LOGS.mkdir(exist_ok=True)
    env = os.environ.copy()
    env.setdefault("LEAN_NUM_THREADS", "1")
    report = {"success": False, "commands": [], "allowed_axioms": sorted(ALLOWED_AXIOMS)}

    def save() -> None:
        (LOGS / "verification.json").write_text(json.dumps(report, indent=2) + "\n")

    def run(args: list[str], name: str) -> str:
        print("Running:", " ".join(args), flush=True)
        started = time.monotonic()
        path = LOGS / name
        with path.open("w") as log:
            result = subprocess.run(args, cwd=LEAN, env=env, stdout=log,
                                    stderr=subprocess.STDOUT)
        report["commands"].append({"argv": args, "exit_code": result.returncode,
                                   "seconds": round(time.monotonic() - started, 2),
                                   "log": str(path.relative_to(ROOT))})
        save()
        if result.returncode:
            raise RuntimeError(f"Command exited {result.returncode}; see {path}")
        return path.read_text()

    try:
        pins = json.loads((ROOT / "SOURCE_PINS.json").read_text())
        patch_file = ROOT / "LOCAL_PATCHES.json"
        patches = json.loads(patch_file.read_text()) if patch_file.exists() else []
        patch_by_path = {patch["path"]: patch for patch in patches}
        report["local_patches"] = patches
        mismatches = []
        checked = 0
        for record in pins["files"]:
            # The root Lake configuration is maintained by this project.
            if record["path"] == "Lean/lakefile.toml":
                continue
            checked += 1
            actual = git_blob((ROOT / record["path"]).read_bytes())
            expected = record["sha"]
            if record["path"] in patch_by_path:
                patch = patch_by_path[record["path"]]
                if patch["source_git_blob"] != record["sha"]:
                    raise RuntimeError("Patch provenance mismatch: " + record["path"])
                expected = patch["patched_git_blob"]
            if actual != expected:
                mismatches.append(record["path"])
        report["source_files_verified"] = checked
        report["source_mismatches"] = mismatches
        if mismatches:
            raise RuntimeError("Imported sources differ from their pins: " + ", ".join(mismatches))

        report["lean_version"] = run(["lean", "--version"], "lean-version.log").strip()
        if "version 4.35.0-rc2," not in report["lean_version"]:
            raise RuntimeError("Unexpected Lean version")

        run(["lake", "build", "CategoricalEssentialIncompleteness"], "build.log")

        deps = []
        manifest = json.loads((LEAN / "lake-manifest.json").read_text())
        for package in manifest["packages"]:
            name = package["name"].removeprefix("«").removesuffix("»")
            folder = LEAN / manifest["packagesDir"] / name
            actual = subprocess.check_output(["git", "rev-parse", "HEAD"],
                                             cwd=folder, text=True).strip()
            deps.append({"name": name, "expected": package["rev"], "actual": actual})
            if actual != package["rev"]:
                raise RuntimeError(f"Dependency revision mismatch: {name}")
        report["dependencies"] = deps

        text = run(["lake", "env", "lean", "CategoricalEssentialIncompleteness/AxiomAudit.lean"], "axiom-audit.log")
        found = {}
        for name, contents in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text):
            found[name] = sorted(x.strip() for x in contents.split(",") if x.strip())
        for name in re.findall(r"'([^']+)' does not depend on any axioms", text):
            found[name] = []
        if set(found) != set(AUDITED):
            raise RuntimeError(f"Axiom audit declaration set differs from the expected {len(AUDITED)} declarations")
        for name, axioms in found.items():
            extra = set(axioms) - ALLOWED_AXIOMS
            if extra:
                raise RuntimeError(f"Unexpected axioms in {name}: {sorted(extra)}")
        report["axioms"] = found
        report["integration_sha256"] = {
            str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
            for path in [LEAN / "CategoricalEssentialIncompleteness.lean", LEAN / "lakefile.toml",
                         *sorted((LEAN / "CategoricalEssentialIncompleteness").glob("*.lean"))]
        }
        report["success"] = True
        save()
        print(f"PASS: project build, dependency pins, source hashes, and {len(AUDITED)} axiom audits.")
        return 0
    except (OSError, RuntimeError, subprocess.SubprocessError) as error:
        report["error"] = str(error)
        save()
        print("FAIL:", error, file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
