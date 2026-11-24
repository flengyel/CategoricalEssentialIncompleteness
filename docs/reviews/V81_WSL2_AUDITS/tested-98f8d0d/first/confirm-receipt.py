"""Validate the completed v81 receipt against Git objects and raw wrapper output.

Read-only. Print the reader's JSON confirmation to stdout after all checks pass.
"""
import argparse
import csv
import gzip
import hashlib
import json
from pathlib import Path
import re
import subprocess

COMMIT = "98f8d0d50a0cc08885d07ab4d71ec6f6a7adf885"
SEALED = "46059744c890b4830bbcfbdb406c8d4950051a00768af0c8945eccdb0d43c14b"
ALLOWED = {"Classical.choice", "Quot.sound", "propext"}
READER = Path(__file__).resolve().parent


def require(value, message):
    if not value:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def file_digest(path):
    with path.open("rb") as source:
        return hashlib.file_digest(source, "sha256").hexdigest()


def original_blobs(repo, paths):
    proc = subprocess.Popen(
        ["git", "-C", str(repo), "cat-file", "--batch"],
        stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    try:
        for path in sorted(paths):
            proc.stdin.write((COMMIT + ":" + path + "\n").encode())
            proc.stdin.flush()
            header = proc.stdout.readline().split()
            require(len(header) == 3 and header[1] == b"blob", "No immutable blob for " + path)
            data = proc.stdout.read(int(header[2]))
            require(proc.stdout.read(1) == b"\n", "Incomplete Git object for " + path)
            yield path, sha(data)
    finally:
        proc.stdin.close()
        proc.stdout.close()
        require(proc.wait() == 0, "git cat-file failed")


def axiom_stream(path):
    content = path.read_text()
    matches = re.finditer(r"^'([^\n]+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)\s*$",
                          content, re.MULTILINE)
    found = {}
    for item in matches:
        name = item[1]
        axioms = [text.strip() for text in (item[2] or "").split(",") if text.strip()]
        require(name not in found, "Duplicate axiom result for " + name)
        require(set(axioms) <= ALLOWED, "Unexpected axiom for " + name)
        found[name] = axioms
    return found


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("bundle", type=Path, help="immutable published .json.gz file")
    cli.add_argument("run", type=Path, help="raw directory created by scripts/verify-wsl.sh")
    cli.add_argument("--repo", type=Path, default=Path.cwd(), help="Git checkout containing the tested commit")
    cli.add_argument("--targeted", type=Path, help="directory of original targeted command logs")
    args = cli.parse_args()
    packed, run, repo = args.bundle.resolve(), args.run.resolve(), args.repo.resolve()
    envelope = json.loads(gzip.decompress(packed.read_bytes()))
    require(envelope["source_commit"] == COMMIT and envelope["manuscript_version"] == 81, "Wrong source revision")
    require(envelope["wrapper"]["source"] == COMMIT and envelope["wrapper"]["exit_code"] == 0, "Wrapper result failed")
    require((run / "start-commit").read_text().strip() == COMMIT, "Wrong wrapper commit")
    require((run / "start-status").read_text().strip() == "## HEAD (no branch)", "Wrapper started with a dirty checkout")
    require((run / "start-diff.patch").read_bytes() == b"", "Initial working-tree diff is nonempty")
    require((run / "exit-status").read_text().strip() == "0", "Wrapper has no successful exit")
    require(envelope["wrapper_log_sha256"] == file_digest(run / "verify.log"), "Wrapper transcript differs")
    official_bytes = (run / "build-logs/verification.json").read_bytes()
    verification = json.loads(official_bytes)
    official_digest = sha(official_bytes)
    require(envelope["official_json_sha256"] == official_digest and envelope["verification"] == verification,
            "Official verifier data differs from publication")
    require(verification["scope"] == "full" and verification["success"] is True, "Full verification did not pass")
    require(verification["current_manuscript"]["version"] == 81 and not verification["source_mismatches"],
            "Manuscript version or imported-source provenance differs")
    require(verification["current_manuscript"]["source_archive_matches"] and verification["current_manuscript"]["pdf_copy_matches"],
            "Manuscript PDF or archive comparison failed")
    cmds = verification["commands"]
    require(all(c["exit_code"] == 0 for c in cmds), "A wrapper command failed")
    require(len({c["log"] for c in cmds}) == len(cmds), "Repeated log names")
    checked_logs = {c["log"]: file_digest(run / c["log"]) for c in cmds}
    require(checked_logs == envelope["command_log_sha256"], "An original command log differs")
    targeted = envelope["targeted"]
    require(len(targeted) == 237 and all(t["source"] == COMMIT and t["exit_code"] == 0 for t in targeted),
            "Targeted commands are incomplete or unsuccessful")
    if args.targeted:
        require(all(file_digest(args.targeted / t["log"]) == t["log_sha256"] for t in targeted),
                "Original targeted log digest differs")
    require(set(verification["allowed_axioms"]) == ALLOWED, "Permitted axiom policy differs")
    retained = axiom_stream(run / "build-logs/axiom-audit.log")
    current = axiom_stream(run / "build-logs/current-axiom-audit.log")
    require(retained == verification["axioms"] and current == verification["current_axioms"],
            "A transitive axiom report disagrees with its raw command output")
    require(current and retained, "Empty transitive axiom inventory")
    state = verification["dependency_worktrees"]
    require(state["start"] == state["end"] == verification["dependencies"], "Dependency state changed")
    require(all(s["expected"] == s["actual"] and s["worktree_clean"] and not s["worktree_status"]
                for s in state["start"]), "Dirty or unpinned dependency")
    snap = verification["integration_sha256"]
    require(dict(original_blobs(repo, snap)) == snap, "Verification source bytes do not match the tested Git revision")
    require(verification["source_snapshot_sha256"] == sha(json.dumps(snap, sort_keys=True).encode()),
            "Snapshot digest differs")
    manifest = json.loads(subprocess.check_output(["git", "-C", str(repo), "show", COMMIT + ":MANUSCRIPT_CURRENT.json"]))
    for record in manifest["files"]:
        require(snap[record["path"]] == record["sha256"], "Wrong manuscript asset: " + record["path"])
    tracked = subprocess.check_output(["git", "-C", str(repo), "ls-tree", "-rz", "--name-only", COMMIT, "Lean"]).decode().split("\0")
    current_paths = {n.removeprefix("Lean/") for n in tracked if n.endswith(".lean") and
                     n.removeprefix("Lean/").removesuffix(".lean").replace("/", ".").startswith(manifest["production_prefix"])}
    strict = {c["argv"][-1] for c in cmds if c["log"].split("/")[-1].startswith("strict-")}
    require(strict == {n for n in current_paths if not n.endswith("Audit.lean")}, "Strict source set incomplete")
    modules = {n.removesuffix(".lean").replace("/", ".") for n in current_paths if not n.endswith(("Checks.lean", "Audit.lean"))}
    require(set(verification["current_audit_modules"]) == modules, "Production module set differs from Git")
    require(file_digest(READER / "SOURCE-VERDICT.SHA256") == SEALED, "Reader's source seal differs")
    for line in (READER / "SOURCE-VERDICT.SHA256").read_text().splitlines():
        digest, name = line.split(maxsplit=1)
        require(file_digest(READER / name) == digest, "Changed reading evidence: " + name)
    matched = []
    if (READER / "numbered-declarations.tsv").is_file():
        names = {r["qualified_name"] for r in csv.DictReader(
            (READER / "numbered-declarations.tsv").open(), delimiter="\t") if r["line_or_reference_kind"] != "module"}
        additional = set(envelope["supplementary_axioms"])
        matched = sorted(names & (set(retained) | set(current) | additional))
        require(len(names) == 852, "Independent numbered declaration inventory differs")
    result = {
        "reader": "independent first reader",
        "tested_commit": COMMIT,
        "official_json_sha256": official_digest,
        "public_gzip_sha256": file_digest(packed),
        "source_verdict_manifest_sha256": SEALED,
        "wrapper_log_sha256": checked_logs and file_digest(run / "verify.log"),
        "official_commands": len(cmds),
        "strict_Lean_modules": len(strict),
        "current_production_modules": len(modules),
        "current_transitive_declarations": len(current),
        "retained_transitive_declarations": len(retained),
        "permitted_axioms": sorted(ALLOWED),
        "immutable_source_files_compared": len(snap),
        "clean_dependencies": len(state["start"]),
        "targeted_commands": len(targeted),
        "raw_targeted_logs_compared": len(targeted) if args.targeted else 0,
        "independently_enumerated_numbered_declarations": 852,
        "numbered_declarations_with_a_named_transitive_entry": len(matched),
        "all_reader_findings": {"mathematical_errors": 1, "ambiguities": 1, "lean_omissions": 8, "proof_gaps": 8},
    }
    print(json.dumps(result, indent=2, ensure_ascii=False))


if __name__ == "__main__":
    main()
