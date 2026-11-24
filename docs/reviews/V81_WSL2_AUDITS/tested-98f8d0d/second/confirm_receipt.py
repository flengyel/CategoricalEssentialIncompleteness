"""Independently verify the original complete v81 replay and its canonical bundle.

Give --official the uncompressed verification.json preserved by the successful
wrapper, --bundle the canonical .json.gz, --targeted-logs the actual targeted
logs, and --repo the repository containing the tested commit. Output is a
detached confirmation. No files in the repository or bundle are changed.
"""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import re
import subprocess


TESTED = "98f8d0d50a0cc08885d07ab4d71ec6f6a7adf885"
PAPER = "986dee4d54d202a452009146cc29d19a544b0000"
POLICY = {"Classical.choice", "Quot.sound", "propext"}
SEAL = "ce37a74d35bcec8cc5a1b4f8c94daeaf3a2350b62f1ba717f2ad6e7b3570a280"
REPORT = "c2d8d7f791bcd131eaaf4a6aa4cbed430bf776352d7f9a2f9bf88e63fb5093ef"
COUNT = dict(mathematical_errors=1, ambiguities=1, lean_omissions=8, proof_gaps=8)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def git(repository, *args):
    return subprocess.check_output(["git", *args], cwd=repository)


def compare_file_batch_to_git(repository, rev, measured, named_blobs):
    tree = {}
    for line in git(repository, "ls-tree", "-rz", rev).split(b"\0"):
        if line:
            metadata, path = line.split(b"\t", 1)
            tree[path.decode()] = metadata.split()[2].decode()
    require(measured.keys() == named_blobs.keys(), "measured source path sets differ")
    with subprocess.Popen(["git", "cat-file", "--batch"], cwd=repository,
                          stdin=subprocess.PIPE, stdout=subprocess.PIPE) as proc:
        for path, digest in measured.items():
            blob_id = tree[path]
            require(blob_id == named_blobs[path], "pinned Git entry mismatch: "+path)
            proc.stdin.write(blob_id.encode()+b"\n")
            proc.stdin.flush()
            tag = proc.stdout.readline().split()
            require(len(tag) == 3 and tag[0].decode() == blob_id and tag[1] == b"blob",
                    "invalid Git object: "+path)
            data = proc.stdout.read(int(tag[2]))
            require(proc.stdout.read(1) == b"\n" and sha(data) == digest,
                    "measured bytes differ from target Git object: "+path)
        proc.stdin.close()
        require(proc.wait() == 0, "git cat-file failed")
    return tree


def axiom_lines(log):
    pattern = re.compile(r"^'(.+?)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)\s*$", re.M)
    output = {}
    for name, values in pattern.findall(log):
        require(name not in output, "duplicate axiom report for "+name)
        output[name] = sorted(v.strip() for v in values.split(",") if v.strip())
    return output


def read_sealed_claims(directory):
    require(sha((directory/"SHA256SUMS").read_bytes()) == SEAL, "reader seal differs")
    for entry in (directory/"SHA256SUMS").read_text().splitlines():
        expected, path = entry.split(maxsplit=1)
        require(sha((directory/path).read_bytes()) == expected, "reader evidence changed: "+path)
    require(sha((directory/"report.md").read_bytes()) == REPORT, "verdict changed")
    combined = gzip.decompress((directory/"checked-types.txt.gz").read_bytes()).decode()
    numbered, last = combined.split("=== CheckLiterature.lean ===")
    names = set(re.findall(r"^#check @([\w.']+)$", numbered, re.M))
    seven = axiom_lines(last)
    require(len(names)==852 and len(seven)==7, "reader declaration inventory changed")
    return names, seven


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--official", type=Path, required=True)
    parser.add_argument("--bundle", type=Path, required=True)
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--targeted-logs", type=Path, required=True)
    parser.add_argument("--reader-files", type=Path, default=Path(__file__).resolve().parent/"publication")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    original = args.official.resolve()
    run = original.parent.parent
    checked = original.read_bytes()
    raw = args.bundle.read_bytes()
    bundle = json.loads(gzip.decompress(raw))
    v = json.loads(checked)
    require(bundle["source_commit"] == TESTED and bundle["manuscript_commit"] == PAPER
            and bundle["manuscript_version"] == 81, "wrong source in canonical bundle")
    require(bundle["official_json_sha256"] == sha(checked) and v == bundle["verification"],
            "standalone verifier JSON and canonical receipt differ")
    require(json.dumps(v,indent=2).encode()+b"\n" == checked,
            "embedded official JSON fails canonical byte reproduction")
    require(v["scope"]=="full" and v["success"] is True and not v["source_mismatches"],
            "official replay did not finish with full verified scope")
    ms = v["current_manuscript"]
    require(ms["version"]==81 and ms["tex_files"]==25 and ms["source_archive_matches"]
            and ms["pdf_copy_matches"], "wrong or incomplete manuscript inputs")
    require(bundle["wrapper"]["source"]==TESTED and bundle["wrapper"]["exit_code"]==0
            and (run/"start-commit").read_text().strip()==TESTED
            and (run/"exit-status").read_text().strip()=="0"
            and (run/"start-status").read_text().strip()=="## HEAD (no branch)"
            and (run/"start-diff.patch").read_bytes()==b""
            and sha((run/"verify.log").read_bytes())==bundle["wrapper_log_sha256"],
            "detached wrapper failed clean start/output validation")
    require(v["dependency_worktrees"]["start"]==v["dependency_worktrees"]["end"]
            and len(v["dependencies"])==16
            and all(d["expected"]==d["actual"] and d["worktree_clean"] for d in v["dependencies"]),
            "dependency pins or worktrees differ")
    require(not git(args.repo,"diff","--name-only",PAPER,TESTED,"--","manuscript/latex"),
            "tested paper differs from blind paper")
    files = compare_file_batch_to_git(args.repo, TESTED, v["integration_sha256"],
                                      bundle["verified_commit_git_blobs"])
    prefix = "Lean/CategoricalEssentialIncompleteness/"
    import_files = {p[len(prefix):] for p in files if p.startswith(prefix+"V46")
                    and p.endswith(".lean") and "/" not in p[len(prefix):]}
    current = {"CategoricalEssentialIncompleteness."+f[:-5] for f in import_files
               if not f.endswith(("Checks.lean","Audit.lean"))}
    require(current==set(v["current_audit_modules"]), "current production-module coverage differs")
    strict_files = {"CategoricalEssentialIncompleteness/"+f for f in import_files if not f.endswith("Audit.lean")}
    strict_files.update({"CategoricalEssentialIncompleteness/CurrentStatementAudit.lean",
                         "CategoricalEssentialIncompleteness/CurrentAxiomAudit.lean"})
    actual_strict = {c["argv"][-1] for c in v["commands"] if "-DwarningAsError=true" in c["argv"]}
    require(strict_files==actual_strict and len(v["commands"])==len(strict_files)+6,
            "official strict coverage differs from the tested module tree")
    log_names=set()
    for check in v["commands"]:
        rel=check["log"]
        require(check["exit_code"]==0 and rel not in log_names
                and sha((run/rel).read_bytes())==bundle["command_log_sha256"][rel],
                "official transcript mismatch: "+rel)
        log_names.add(rel)
    require(log_names==set(bundle["command_log_sha256"]), "additional official log in receipt")
    require(set(v["allowed_axioms"])==POLICY, "permitted axioms changed")
    all_axioms={}
    for group in [v["axioms"], v["current_axioms"], bundle["supplementary_axioms"]]:
        for name,deps in group.items():
            values=sorted(deps)
            require(set(values)<=POLICY and (name not in all_axioms or all_axioms[name]==values),
                    "conflicting or nonpermitted axiom report for "+name)
            all_axioms[name]=values
    for file, names in [("axiom-audit.log",v["axioms"]),("current-axiom-audit.log",v["current_axioms"])]:
        require(axiom_lines((original.parent/file).read_text())=={n:sorted(x)for n,x in names.items()},
                "transitive audit transcript does not reproduce "+file)
    targets=bundle["targeted"]
    require(len(targets)==237, "targeted check count differs")
    for c in targets:
        require(c["source"]==TESTED and c["exit_code"]==0
                and sha((args.targeted_logs/c["log"]).read_bytes())==c["log_sha256"],
                "targeted transcript differs: "+c["log"])
    adopted, side = read_sealed_claims(args.reader_files)
    require(adopted<=all_axioms.keys(), "reader reference(s) missing transitive coverage: "+
            str(sorted(adopted-all_axioms.keys())))
    require(all(n in all_axioms and all_axioms[n]==ax for n,ax in side.items()),
            "reader literature axiom probe disagrees with official replay")
    canonical_rows=bundle["numbered_correspondence"]
    canonical={}
    for row in canonical_rows:
        for item in row["references"]:
            if not item["module_or_collection"]:
                name=item["declaration"]
                require(name in all_axioms and sorted(item["axioms"])==all_axioms[name],
                        "canonical numbered application missing: "+name)
                canonical[name]=item["source"]
    require(len(canonical_rows)==80 and len(canonical)==844,
            "canonical numbered corrspondence changed")
    require(len(adopted&canonical.keys())==836, "relationship between numbered inventories changed")
    for passage, rows in bundle["v81_passage_applications"].items():
        require(rows, "empty passage application: "+passage)
    require(len(bundle["independent_audits"])==2
            and all(a["source_commit"]==TESTED and a["counts"]==COUNT for a in bundle["independent_audits"])
            and any(REPORT in a["files_sha256"].values() for a in bundle["independent_audits"]),
            "independent findings or report files differ")
    out = dict(tested_commit=TESTED,manuscript_commit=PAPER,manuscript_version=81,
               official_json_sha256=sha(checked),bundle_sha256=sha(raw),
               compressed_receipt_sha256=sha(raw),reader_verdict_sha256=REPORT,
               reader_seal_sha256=SEAL,clean_detached_wrapper_exit=0,
               official_commands=len(v["commands"]),official_strict_commands=len(strict_files),
               official_log_hashes_checked=len(log_names),targeted_log_hashes_checked=len(targets),
               identical_pinned_clean_dependencies=len(v["dependencies"]),source_blobs_checked=len(v["integration_sha256"]),
               production_modules=len(current),current_axioms=len(v["current_axioms"]),
               retained_axioms=len(v["axioms"]),supplementary_axioms=len(bundle["supplementary_axioms"]),
               allowed_axioms=sorted(POLICY),numbered_items=len(canonical_rows),
               reader_named_declarations_confirmed=len(adopted),canonical_numbered_declarations=len(canonical),
               both_numbered_inventories_intersection=len(adopted&canonical.keys()),
               reader_only_numbered_declarations=sorted(adopted-canonical.keys()),
               canonical_only_numbered_declarations=sorted(canonical.keys()-adopted),
               named_literature_reader_axiom_reports_confirmed=side,independent_counts=COUNT,
               clean_streak=0,signer="Independent second reader")
    data=(json.dumps(out,ensure_ascii=False,indent=2)+"\n").encode()
    if args.output.exists():
        require(args.output.read_bytes()==data,"a distinct confirmation already exists")
    else:
        args.output.write_bytes(data)
    print("Verified",out["official_commands"],"official commands and both numbered inventories.",
          "Confirmation SHA-256",sha(data))


if __name__=="__main__":
    main()
