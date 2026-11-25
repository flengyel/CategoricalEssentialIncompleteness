# WSL2 replay of manuscript v93

Run the full Lean verification against one public v93 commit, publish the receipt and two independent readings on `origin/main`, then return the tested SHA and report SHA for Palomar re-registration. The [manifest](../MANUSCRIPT_CURRENT.json) selects the paper and the [correspondence](../FORMALIZATION_STATUS_V93.md) identifies its Lean declarations. A v84 serial replay took 4 hours 22 minutes.

## Start in WSL2 Debian

Use the Linux filesystem and the existing checkout. The commands below create a detached worktree and preserve any work in the existing checkout. Run the shell blocks in order in the same Bash session. When the launch prompt supplies an exact SHA, set `cei_requested` to it before executing this block. Otherwise the fetched tip is the candidate. A later remote commit can coexist with a replay pinned to the requested public ancestor.

```bash
set -euo pipefail
cei_repo=/home/flengyel/src/CategoricalEssentialIncompleteness
cd "$cei_repo"
git fetch origin main
cei_sha=$(git rev-parse "${cei_requested:-origin/main}^{commit}")
git merge-base --is-ancestor "$cei_sha" origin/main
cei_work=$(mktemp -d /home/flengyel/src/cei-v93-replay-XXXXXXXX)
git worktree add --detach "$cei_work" "$cei_sha"
cd "$cei_work"
test "$(git rev-parse HEAD)" = "$cei_sha"
test -z "$(git status --porcelain)"
python3 -c 'import json; assert json.load(open("MANUSCRIPT_CURRENT.json"))["version"] == 93'
export PATH="$HOME/.elan/bin:$PATH" LEAN_NUM_THREADS=1
elan toolchain install "$(cat Lean/lean-toolchain)"
(cd Lean && lean --version && lake --version && lake exe cache get)
```

The pin is `leanprover/lean4:v4.35.0-rc2`. Keep the manifest revisions when obtaining dependencies. The official verifier checks the pinned dependency worktrees for cleanliness at both ends of the run.

## Replay and monitor to completion

The [v84 receipt](V84_WSL2_LEAN_VERIFICATION.json.gz) includes a reusable list of supplemental commands and the source of its final standard-input query. Execute the commands against v93 and capture their new results. They include the parser tests, manuscript-only check, targeted build, strict module checks and named type/axiom queries. The wrapper then runs the full kernel and axiom audit. This sequence calls the official wrapper once. The alternative bootstrap script `setup-wsl.sh` already calls that wrapper.

```bash
mkdir -p .codex-work/v93-targeted
python3 - <<'PY'
from pathlib import Path
from datetime import datetime, timezone
import gzip, hashlib, json, subprocess

root = Path.cwd()
evidence = root / ".codex-work/v93-targeted"
with gzip.open(root / "docs/V84_WSL2_LEAN_VERIFICATION.json.gz", "rt") as source:
    recipe = json.load(source)
sha = subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip()
query = recipe["passage_query"]["source"].encode()
(evidence / "passages.lean").write_bytes(query)
records = []
for job in recipe["targeted_commands"]:
    args = job["argv"]
    stdin = query if "--stdin" in args else None
    if stdin is not None:
        assert hashlib.sha256(stdin).hexdigest() == job["stdin_sha256"]
    log = evidence / (job["label"] + ".log")
    started = datetime.now(timezone.utc)
    with log.open("wb") as out:
        result = subprocess.run(args, cwd=root / job["cwd"], input=stdin,
                                stdout=out, stderr=subprocess.STDOUT)
    records.append(dict(source_commit=sha, label=job["label"], argv=args,
                        cwd=job["cwd"], started_utc=started.isoformat(),
                        ended_utc=datetime.now(timezone.utc).isoformat(),
                        exit_code=result.returncode, log=log.name,
                        log_sha256=hashlib.sha256(log.read_bytes()).hexdigest(),
                        stdin_sha256=hashlib.sha256(stdin).hexdigest() if stdin is not None else None))
    (evidence / "commands.json").write_text(json.dumps(records, indent=2) + "\n")
    print(job["label"], result.returncode, flush=True)
    if result.returncode:
        raise SystemExit(f"Failed: {log}")
PY
bash scripts/verify-wsl.sh
```

Keep the session running through completion. From a second terminal, use the worktree path printed by Git to find the current `.codex-work/verify-*/verify.log` and follow it with `tail -f`. The wrapper records `start-commit`, `start-status`, the initial diff, and `exit-status`; on exit it copies the logs into that run directory. An interrupted or unsuccessful attempt keeps its own evidence. Diagnose the first failed command before retrying. If a tracked proof or input requires correction, commit the correction and replay the revised SHA.

## Verify and publish the evidence

In the fresh worktree, select the run whose start-commit is the tested SHA and which has just completed. Inspect the saved full report. The following check reads the most recent wrapper run in this worktree.

```bash
python3 - <<'PY'
from pathlib import Path
import json, subprocess
run = max(Path(".codex-work").glob("verify-*"), key=lambda p:p.stat().st_mtime_ns)
sha = subprocess.check_output(["git","rev-parse","HEAD"], text=True).strip()
assert (run/"start-commit").read_text().strip() == sha
assert (run/"exit-status").read_text().strip() == "0"
assert (run/"start-diff.patch").stat().st_size == 0
report = json.loads((run/"build-logs/verification.json").read_text())
assert report["scope"] == "full" and report["success"]
assert report["current_manuscript"]["version"] == 93
assert report["commands"] and all(c["exit_code"] == 0 for c in report["commands"])
allowed = {"propext", "Quot.sound", "Classical.choice"}
for k in ("current_axioms","axioms"):
    assert report[k] and all(set(xs) <= allowed for xs in report[k].values())
for stage in ("start", "end"):
    deps = report["dependency_worktrees"][stage]
    assert deps and all(p["actual"] == p["expected"] and p["worktree_clean"] for p in deps)
print(sha, run, len(report["commands"]), len(report["current_axioms"]), len(report["axioms"]))
PY
```

1. Assemble `docs/V93_WSL2_LEAN_VERIFICATION.json.gz` from the fresh official JSON and supplemental logs. The wrapper writes the official JSON under `build-logs/`; the versioned receipt is a separate deliverable. Include source SHA, UTC times, durations, exit codes, toolchain, dependency revisions, command and log digests, measured input hashes and Git blobs, current and retained transitive axioms, and the query source and result. Record failed attempts separately. Derive all counts from the v93 run. See the [v84 report and receipt](V84_WSL2_LEAN_VERIFICATION.md) for the evidence format.
2. Write `docs/V93_WSL2_LEAN_VERIFICATION.md` and the two full independent readings under `docs/reviews/V93_WSL2_AUDITS/`. Follow [AGENTS.md](../AGENTS.md) on **the same tested source**. Reconcile all 77 numbered results, the three numbered definitions, the unnumbered arguments and the external results the proofs use. In §1 check the type of the copairing and the section-to-range argument. In C.1 compare the arbitrary second coordinate and the quantifier over every candidate lift; in A.7 check both range inequalities. Preserve the distinctions checked in the [v92 report](reviews/V92_REFEREE_AND_WRITING/README.md). If either reader finds a discrepancy, record and resolve it before claiming a clean reading.
3. Publish the evidence in a report-only commit on `origin/main`, preserving any concurrent work and using a non-force push. Fetch again and compare every measured input with its tested blob. Report any difference; identify the tested commit independently of later commits. Return both SHAs and working links to the report, receipt and reconciled readings.

## After the replay

The next task is re-registration of existing Palomar entry `PALOMAR-2026-11-22-000009`. The v93 PDF still cites registered version 3 and the tag `cei-v72-palomar-v3`. Check the public version history and pending attempts before choosing the next version. Use the [Palomar procedure](CODEX_WSL2_PALOMAR_SUBMISSION.md) for the fresh candidate tag, manuscript links, metadata and official preflight. If those changes alter measured inputs, record the new candidate and its verification separately. The WSL2 replay receipt identifies the exact commit it tested.
