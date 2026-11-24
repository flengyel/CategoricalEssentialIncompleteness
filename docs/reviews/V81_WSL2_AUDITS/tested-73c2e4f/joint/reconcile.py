"""Recheck the two sealed v81 reader packages and compare their findings, rows, and axiom lists."""

import argparse
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path
import re
import tarfile

TESTED = "73c2e4fa2bc633a3af012b1c4f85a7882018f962"
READING = "ae816e93c11712a2b1fe16f99c763a8c934f80dc"
ALLOWED = {"Classical.choice", "Quot.sound", "propext"}
ISSUES = {
    "H1": "Bauer–Hanson 6.4",
    "H2": "Heller 9.2",
    "H3": "Lengyel 21",
    "H4": "Lengyel corrected 26",
    "T1": "Di Paola–Heller 8.15",
    "H5": "van Dijk–Gietelink Oldenziel 5.19",
    "H6": "van Dijk–Gietelink Oldenziel 5.20",
    "B1": "Page of Di Paola–Heller item (3)",
    "T2": "Effective extensibility",
    "T3": "Two types of d",
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(blob):
    return hashlib.sha256(blob).hexdigest()


def member(archive, name):
    return archive.extractfile(name).read()


def verify_manifest(data, read):
    result = {}
    for line in data.decode().splitlines():
        expected, filename = line.split(maxsplit=1)
        filename = filename.strip()
        require(digest(read(filename)) == expected, "Digest differs for " + filename)
        result[filename] = expected
    return result


def reader_files(path):
    hashes = verify_manifest((path / "SHA256SUMS").read_bytes(), lambda name: (path / name).read_bytes())
    verdict = json.loads((path / "verdict.json").read_bytes())
    require(verdict["source_commit"] == TESTED and verdict["manuscript_version"] == 81, "Wrong tested source")
    return hashes, verdict


def transitive_outputs(data):
    entries = {}
    for name, values in re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]", data, re.MULTILINE):
        require(name not in entries, "Repeated axiom entry " + name)
        entries[name] = {x.strip() for x in values.split(",") if x.strip()}
    for name in re.findall(r"^'([^']+)' does not depend on any axioms", data, re.MULTILINE):
        require(name not in entries, "Repeated axiom entry " + name)
        entries[name] = set()
    return entries


def early_seals(first, second):
    manifests = {}
    with tarfile.open(first / "manuscript-reading.tar.gz") as archive:
        seal = member(archive, "first-reading.sha256")
        verify_manifest(seal, lambda filename: member(archive, filename))
        manifests["first"] = {"file": "first-reading.sha256", "sha256": digest(seal)}
        tex = verify_manifest(member(archive, "tex.sha256"), lambda f: member(archive, f))
    with tarfile.open(second / "blind-reading.tar.gz") as archive:
        seal = member(archive, "seal.sha256")
        verify_manifest(seal, lambda filename: member(archive, Path(filename).name))
        manifests["second"] = {"file": "seal.sha256", "sha256": digest(seal)}
        rows = member(archive, "tex-order.tsv").decode().splitlines()
    expected = {row.split("\t")[0]: row.split("\t")[2] for row in rows}
    require(len(expected) == 25 and expected == {k.removeprefix("tex/"): v for k, v in tex.items()}, "Sealed TeX differs")
    return manifests


def compare_issues(first, second):
    first_issues = {x["id"]: x for x in first["issues"]}
    second_issues = {x["id"]: x for x in second["issues"]}
    require(set(first_issues) == set(ISSUES.values()) and set(second_issues) == set(ISSUES), "Issue identity differs")
    compared = {}
    for code, name in ISSUES.items():
        left = first_issues[name]
        right = second_issues[code]
        path, locator = left["TeX"].rsplit(":", 1)
        require(path == right["source_file"], name + " source file differs")
        kinds = {x.replace("_", " ").lower() for x in left["categories"]}
        require(kinds == {x.lower() for x in right["category"]}, name + " category differs")
        compared[code] = {
            "first_reader_id": name, "categories": sorted(kinds), "source": path,
            "first_reader_lines": locator, "second_reader_lines": right["lines"],
        }
    return compared


def compare_checks(first, second):
    with tarfile.open(first / "proof-comparison.tar.gz") as archive:
        rows1 = json.loads(member(archive, "numbered-types.json"))["rows"]
        captured1 = json.loads(member(archive, "numbered-axioms.json"))["declarations"]
        first_test = json.loads(member(archive, "IndependentChecks.json"))
        first_log = member(archive, "IndependentChecks.log")
        require(digest(member(archive, "IndependentChecks.lean")) == first_test["source_sha256"], "Reader one test hash")
        require(digest(first_log) == first_test["log_sha256"], "Reader one test output hash")
        require(first_test["source_commit"] == TESTED and first_test["exit"] == 0, "Reader one test failed")
    with tarfile.open(second / "proof-checks.tar.gz") as archive:
        rows2 = json.loads(gzip.decompress(member(archive, "numbered.json.gz")))["rows"]
        captured2 = transitive_outputs(member(archive, "numbered.log").decode())
        kernel = json.loads(member(archive, "kernel.json"))
        second_test = kernel["probes"]["Applications"]
        second_log = member(archive, "probe.log")
        require(digest(member(archive, "Applications.lean")) == second_test["source_sha256"], "Reader two test hash")
        require(digest(second_log) == second_test["output_sha256"], "Reader two test output hash")
        require(kernel["source_commit"] == TESTED and second_test["exit_code"] == 0, "Reader two test failed")
    require(len(rows1) == len(rows2) == 80, "Numbered count differs")
    summary = []
    referenced = set()
    for row in rows1:
        number = row["number"]
        other = rows2[number]
        require(row["label"] == other["label"] and row["source"] == other["source"], number + " TeX identity differs")
        require(other["lines"][0] <= row["tex_line"] <= other["lines"][1], number + " location differs")
        require(other["correspondence"] == "FORMALIZATION_STATUS_V81.md#L" + str(row["ledger_line"]), number + " ledger differs")
        names = set(row["direct"])
        require(names == set(other["explicit_qualified_names"]), number + " direct declarations differ")
        referenced.update(names)
        summary.append({
            "number": number, "kind": row["kind"], "label": row["label"], "ledger_line": row["ledger_line"],
            "direct_name_count": len(names),
        })
    require(len(referenced) == 852 and referenced == set(captured2), "Direct declaration coverage differs")
    for name in referenced:
        require(set(captured1[name]["axioms"]) == captured2[name] <= ALLOWED, "Axiom lists differ for " + name)
    numerical = [
        {
            "reader": "first",
            "theorem": "IndependentV81Reader.membership_in_the_printed_algebra",
            "source": "IndependentChecks.lean",
            "source_sha256": first_test["source_sha256"],
            "output_sha256": first_test["log_sha256"],
            "type": "Separate total computable term and formula predicates on every word in the two supports of NumericalNamed.literalWordAlgebra.",
        },
        {
            "reader": "second",
            "theorem": "V81SecondReading.simultaneous_support_decision",
            "source": "Applications.lean",
            "source_sha256": second_test["source_sha256"],
            "output_sha256": second_test["output_sha256"],
            "type": "A total computable function returning both membership bits on every word in the two unary NumericalCoordinates.predicateObject supports of the literal postfix carriers.",
        },
    ]
    for row, log in zip(numerical, (first_log, second_log)):
        entries = transitive_outputs(log.decode())
        require(row["theorem"] in entries and entries[row["theorem"]] <= ALLOWED, "Numerical test axiom coverage differs")
        row["transitive_axioms"] = sorted(entries[row["theorem"]])
    return summary, numerical


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("first", type=Path)
    parser.add_argument("second", type=Path)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()
    first_hashes, first = reader_files(args.first)
    second_hashes, second = reader_files(args.second)
    require(first["reading_source_commit"] == second["independence"]["blind_source_commit"] == READING, "Reading revision differs")
    seals = early_seals(args.first, args.second)
    require(seals["first"]["sha256"] == first["independence"]["first_reading_manifest_sha256"], "First early seal differs from verdict")
    require(first["four_counts"] == second["counts"], "Four verdict counts differ")
    require(first["proof_gaps_including_missing_kernel_proofs"] == second["counting_convention"]["broader_proof_gap_count_including_missing_formal_proofs"] == 7, "Inclusive gap count differs")
    require(first["numbered_proof_gaps"] == second["numbered_proof_gaps"] == 0, "Numbered gap count differs")
    require(first["bibliographic_locators"] == second["counting_convention"]["bibliographic_locators"] == 1, "Bibliographic count differs")
    require(first["qualifying_count"] == second["qualifying_clean_reports"] == 0, "Qualifying count differs")
    compared_issues = compare_issues(first, second)
    numbered_rows, numerical = compare_checks(args.first, args.second)
    here = Path(__file__).resolve().parent
    support_log = (here / "NumericalSupports.log").read_bytes()
    support_axioms = transitive_outputs(support_log.decode())
    require(set(support_axioms) == {"V81Reconciliation.literal_supports"}, "Wrong support equality")
    require(support_axioms["V81Reconciliation.literal_supports"] <= ALLOWED, "Unexpected axiom in support equality")
    result = {
        "source_commit": TESTED,
        "blind_reading_source_commit": READING,
        "verdict_and_report_sha256": {
            "first": {name: first_hashes[name] for name in ("verdict.json", "report.md")},
            "second": {name: second_hashes[name] for name in ("verdict.json", "report.md")},
        },
        "original_reading_seals": seals,
        "active_TeX_digests_identical": 25,
        "four_counts": first["four_counts"],
        "counting_convention": second["counting_convention"],
        "numbered_proof_gaps": 0,
        "qualifying_clean_reports": 0,
        "required_consecutive_clean_reports": 2,
        "issues": compared_issues,
        "numbered_kind_counts": dict(Counter(x["kind"] for x in numbered_rows)),
        "shared_numbered_direct_declarations_and_individual_axiom_sets": 852,
        "numbered_rows": numbered_rows,
        "numerical_tests": numerical,
        "postseal_numerical_support_equality": {
            "declaration": "V81Reconciliation.literal_supports",
            "source_sha256": digest((here / "NumericalSupports.lean").read_bytes()),
            "output_sha256": digest(support_log),
            "Lean_flags": ["-j1", "-DwarningAsError=true", "-DautoImplicit=false"],
            "exit_code": 0,
            "axioms": sorted(support_axioms["V81Reconciliation.literal_supports"]),
        },
        "material_disagreements": [],
    }
    serialized = json.dumps(result, indent=2, ensure_ascii=False) + "\n"
    if args.out:
        args.out.write_text(serialized)
    else:
        print(serialized, end="")


if __name__ == "__main__":
    main()
