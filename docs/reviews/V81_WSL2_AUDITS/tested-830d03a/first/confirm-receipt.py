"""Compare the original v81 wrapper, frozen Git objects, and first-reader probes."""

import argparse
import gzip
import hashlib
import json
from pathlib import Path
import re
import subprocess


TESTED = "830d03a5adcf144a003feb36f88bd06e0c5b0cf5"
HERE = Path(__file__).resolve().parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def require(condition, description):
    if not condition:
        raise ValueError(description)


def git(*arguments):
    return subprocess.check_output(["git", *arguments], cwd=HERE)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def read_frozen_json(path):
    return json.loads(git("show", f"{TESTED}:{path}"))


def axiom_reports(transcript, *, repeat_identical=False):
    """Keep primes in names and accept multiline lists returned by Lean."""
    pattern = re.compile(
        r"^'(?P<name>[^\n]+)' (?:does not depend on any axioms|"
        r"depends on axioms:\s*\[(?P<axioms>[^\]]*)\])\s*$", re.MULTILINE
    )
    reports = {}
    for match in pattern.finditer(transcript):
        name = match["name"]
        words = (match["axioms"] or "").split(",")
        axioms = sorted(word.strip() for word in words if word.strip())
        require(set(axioms) <= ALLOWED, f"Unexpected axiom in {name}")
        if name in reports:
            require(repeat_identical and reports[name] == axioms, f"Repeated or conflicting axiom report for {name}")
        reports[name] = axioms
    return reports


def compare_git_blobs(records):
    # Read the exact objects even when the local branch has advanced since the replay.
    with subprocess.Popen(
        ["git", "cat-file", "--batch"], cwd=HERE,
        stdin=subprocess.PIPE, stdout=subprocess.PIPE,
    ) as process:
        try:
            for path, expected in records.items():
                process.stdin.write(f"{TESTED}:{path}\n".encode())
                process.stdin.flush()
                header = process.stdout.readline().split()
                require(len(header) == 3 and header[1] == b"blob", f"Missing Git blob {path}")
                data = process.stdout.read(int(header[2]))
                require(process.stdout.read(1) == b"\n", f"Incomplete output for {path}")
                require(sha256(data) == expected, f"Commit and wrapper differ for {path}")
        finally:
            process.stdin.close()
        require(process.wait() == 0, "Git could not read every source object")


def verify_dependencies(verification, run):
    manifest = read_frozen_json("Lean/lake-manifest.json")
    require(json.loads((run / "lake-manifest.json").read_bytes()) == manifest, "Dependency manifest differs")
    toolchain = git("show", f"{TESTED}:Lean/lean-toolchain")
    require((run / "lean-toolchain").read_bytes() == toolchain, "Lean toolchain pin differs")
    expected = {p["name"].strip("«»"): p["rev"] for p in manifest["packages"]}
    for stage in ("start", "end"):
        states = verification["dependency_worktrees"][stage]
        package_pins = {state["name"]: state["actual"] for state in states}
        require(package_pins == expected and len(states) == len(expected), f"Incorrect {stage} package pins")
        for state in states:
            require(state["expected"] == state["actual"], f"Revision mismatch for {state['name']}")
            require(state["worktree_clean"] and not state["worktree_status"], f"Dirty {stage} package {state['name']}")
    return len(expected)


def compare_manuscript(verification):
    manifest = read_frozen_json("MANUSCRIPT_CURRENT.json")
    require(manifest["version"] == 81, "The pinned target is not manuscript v81")
    snapshot = verification["integration_sha256"]
    for item in manifest["files"]:
        require(snapshot.get(item["path"]) == item["sha256"], f"Manifest mismatch for {item['path']}")
    blind = {}
    for line in (HERE / "paper-inputs.sha256").read_text().splitlines():
        digest, name = line.split("  ", 1)
        blind["manuscript/latex/" + name.removeprefix("paper/")] = digest
    wrapper_tex = {p: d for p, d in snapshot.items() if p.startswith("manuscript/latex/") and p.endswith(".tex")}
    require(blind == wrapper_tex and len(blind) == 25, "The blinded and wrapper TeX inputs differ")
    return manifest, len(blind)


def compare_commands(verification, manifest):
    commands = verification["commands"]
    require(commands and all(command["exit_code"] == 0 for command in commands), "Nonzero command or empty replay")
    invocation = [command["argv"] for command in commands]
    strict = {args[-1] for args in invocation if "-DwarningAsError=true" in args and args[-1].endswith(".lean")}
    lean_paths = git("ls-tree", "-r", "--name-only", TESTED, "Lean").decode().splitlines()
    prefix = "Lean/" + manifest["production_prefix"].replace(".", "/")
    production_sources = {p.removeprefix("Lean/") for p in lean_paths if p.startswith(prefix) and p.endswith(".lean")}
    expected_strict = {p for p in production_sources if not Path(p).stem.endswith("Audit")}
    expected_strict.update(manifest[key].replace(".", "/") + ".lean" for key in ("statement_audit", "axiom_audit"))
    require(strict == expected_strict, f"Strict source set differs at {sorted(strict ^ expected_strict)}")
    expected_modules = {p.removesuffix(".lean").replace("/", ".") for p in production_sources
                        if not Path(p).stem.endswith(("Audit", "Checks"))}
    actual = verification["current_audit_modules"]
    require(set(actual) == expected_modules and len(actual) == len(expected_modules), "Current module coverage differs")
    require(["lake", "build", "CategoricalEssentialIncompleteness"] in invocation, "Missing project build")
    require(["lake", "build", manifest["statement_audit"]] in invocation, "Missing current statement build")
    for file in ("AxiomAudit", "V5StatementAudit"):
        expected = f"CategoricalEssentialIncompleteness/{file}.lean"
        require(sum(args[-1] == expected for args in invocation) == 1, f"Missing or repeated {file} run")
    return len(strict), len(expected_modules)


def compare_axioms(verification, run):
    audited = {}
    for key, name in (("axioms", "axiom-audit.log"), ("current_axioms", "current-axiom-audit.log")):
        reports = axiom_reports((run / "build-logs" / name).read_text())
        require(reports == verification[key], f"Original {name} and wrapper JSON differ")
        for declaration in audited.keys() & reports.keys():
            require(audited[declaration] == reports[declaration], f"Conflicting audit results for {declaration}")
        audited.update(reports)
    independently_checked = axiom_reports((HERE / "numbered-kernel.log").read_text())
    rows = [json.loads(line) for line in (HERE / "numbered-sources.jsonl").read_text().splitlines()]
    indexed = {entry["name"] for row in rows for entry in row["entries"] if "name" in entry}
    require(indexed == set(independently_checked) and len(indexed) == 844, "Numbered source and Lean queries differ")
    # Statement-check aliases belong to strict check modules. The production audit
    # intentionally omits those modules, so read their actual Lean transcripts too.
    strictly_checked = {}
    for command in verification["commands"]:
        log = command["log"]
        if not Path(log).name.startswith("strict-"):
            continue
        require("-DwarningAsError=true" in command["argv"], f"Expected a strict check for {log}")
        reports = axiom_reports((run / log).read_text(), repeat_identical=True)
        for declaration in indexed & reports.keys():
            require(reports[declaration] == independently_checked[declaration],
                    f"Independent and strict checks differ for {declaration} in {log}")
            if declaration in audited:
                require(reports[declaration] == audited[declaration], f"Conflicting production and strict results for {declaration}")
            strictly_checked.setdefault(declaration, []).append(log)
    for declaration, axioms in independently_checked.items():
        if declaration in audited:
            require(audited[declaration] == axioms, f"Independent and production checks differ for {declaration}")
        else:
            require(declaration in strictly_checked, f"No original axiom output for {declaration}")
    strict_only = {name: strictly_checked[name] for name in sorted(indexed - audited.keys())}
    applications = axiom_reports((HERE / "independent-applications.log").read_text())
    require(len(applications) == 11 and all(n.startswith("FirstReader81.") for n in applications),
            "Expected eleven original-type first-reader proofs")
    return len(indexed), len(applications), strict_only


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run", type=Path, required=True, help="Output directory of the original verify-wsl.sh run")
    parser.add_argument("--packed", type=Path, help="Published consolidated gzip receipt")
    parser.add_argument("--out", type=Path, required=True, help="Write independent receipt comparison as JSON")
    args = parser.parse_args()
    run = args.run
    require((run / "start-commit").read_text().strip() == TESTED, "Wrong tested Git commit")
    require((run / "start-status").read_text().splitlines() == ["## HEAD (no branch)"], "Unclean wrapper start")
    require(not (run / "start-diff.patch").read_bytes(), "The wrapper started with a tracked diff")
    require((run / "exit-status").read_text().strip() == "0", "The wrapper did not complete successfully")
    raw = (run / "build-logs/verification.json").read_bytes()
    verification = json.loads(raw)
    require(verification["success"] and verification["scope"] == "full", "Wrapper did not report full success")
    require(verification["source_mismatches"] == [], "Discrepancy in the wrapper's source comparisons")
    require(set(verification["allowed_axioms"]) == ALLOWED, "Incorrect permitted-axiom list")
    files = verification["integration_sha256"]
    sealed = sha256(json.dumps(files, sort_keys=True).encode())
    require(verification["source_snapshot_sha256"] == sealed, "Integrated snapshot digest differs")
    compare_git_blobs(files)
    packages = verify_dependencies(verification, run)
    manifest, tex_count = compare_manuscript(verification)
    strict, modules = compare_commands(verification, manifest)
    numbered, applications, strict_only = compare_axioms(verification, run)
    result = {
        "tested_git_commit": TESTED,
        "raw_wrapper_json_sha256": sha256(raw),
        "source_snapshot_sha256": sealed,
        "snapshot_files_at_commit": len(files),
        "matched_tex": tex_count,
        "numbered_axioms_matched": numbered,
        "numbered_in_current_or_retained_axiom_audit": numbered - len(strict_only),
        "numbered_axioms_only_in_strict_transcripts": strict_only,
        "independent_original_type_probes": applications,
        "command_count": len(verification["commands"]),
        "strict_sources": strict,
        "retained_declarations": len(verification["axioms"]),
        "current_declarations": len(verification["current_axioms"]),
        "current_modules": modules,
        "pinned_clean_packages_at_start_and_end": packages,
        "commands_exit_zero": True,
        "clean_start": True,
        "scope": verification["scope"],
        "allowed_axioms": sorted(ALLOWED),
    }
    if args.packed:
        compressed = args.packed.read_bytes()
        packed = json.loads(gzip.decompress(compressed))
        require(packed["official_json_sha256"] == sha256(raw), "Consolidated receipt reports a different raw digest")
        require(packed["verification"] == verification, "Consolidated receipt differs from the original wrapper output")
        result["consolidated_receipt_sha256"] = sha256(compressed)
    rendered = json.dumps(result, indent=2) + "\n"
    args.out.write_text(rendered)
    print(rendered, end="")


if __name__ == "__main__":
    main()
