"""Check the two public Lean probes and replay their exported proof dependencies."""

import argparse
import gzip
import hashlib
import json
import os
import re
import shutil
import subprocess
import tarfile
import tempfile
from datetime import datetime, timezone
from pathlib import Path


PIN = "6775f0b3a5fb668f9390b21440f3f6c57bc65930"
PACKAGE = "CategoricalEssentialIncompleteness"
CHECKS = PACKAGE + ".V46ComputableTuringCategoryChecks"
CHECK_NAMESPACE = PACKAGE + ".V46.ComputableTuringCategoryChecks."
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
PROBES = ("PCAObservations", "AmbientProducts")
PRIOR_SEAL = "adc493531652002fd6e268c7b1134c6a2bfd7f680bfef09508948d38d721c3dc"
PCA_MODULES = {
    "V46ApplicativeCodes", "V46ApplicativePolynomials", "V46ComputablePowerInclusion",
    "V46ComputablePowerProducts", "V46ComputablePowerRestriction", "V46ComputablePowerRetractions",
    "V46ComputablePowers", "V46ComputableTuringCategory", "V46ComputableTuringCategoryChecks",
    "V46RestrictionProductCones", "V46SplitIdempotentSubcategory", "V46TuringComputablePowers",
}
bundle = Path(__file__).resolve().parent


def sha(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def checked_output(args, cwd, env=None):
    proc = subprocess.run(args, cwd=cwd, env=env, capture_output=True)
    if proc.returncode:
        raise SystemExit((proc.stdout + proc.stderr).decode(errors="replace"))
    return proc.stdout


def declarations(source, prefix):
    names = re.findall(r"^#print axioms (\w+)$", source.read_text(), re.MULTILINE)
    return [prefix + name for name in names]


def sources_and_objects(repo):
    module_dir = repo / "Lean" / PACKAGE
    obj_dir = repo / "Lean/.lake/build/lib/lean" / PACKAGE
    work = ["V46ComputableTuringCategoryChecks"]
    modules = {}
    while work:
        name = work.pop()
        relative = "Lean/" + PACKAGE + "/" + name + ".lean"
        if name in modules or name not in PCA_MODULES:
            continue
        path = module_dir / (name + ".lean")
        source_digest = sha(path)
        original = checked_output(["git", "show", PIN + ":" + relative], repo)
        if source_digest != hashlib.sha256(original).hexdigest():
            raise ValueError("source disagrees with tested commit: " + relative)
        olean = obj_dir / (name + ".olean")
        modules[name] = {"source_sha256": source_digest, "olean_sha256": sha(olean)}
        work.extend(re.findall(r"^public import " + PACKAGE + r"\.(\w+)$",
                               path.read_text(), re.MULTILINE))
    if modules.keys() != PCA_MODULES:
        raise ValueError("expected twelve new source modules in the statement checks' import graph")
    return dict(sorted(modules.items()))


def verify_history(repo, current):
    edits = {
        "V46ApplicativeCodes": ("Iterated application of a code point",
                                "Iterated application of a fixed point"),
        "V46ComputablePowerProducts": ("Its domain is the intersection of the two component domains.",
                                       "Its domain includes both components."),
        "V46SplitIdempotentSubcategory": (
            "If every ambient object is a retract of an object in the image of a fully\n"
            "faithful functor, splitting the idempotents in this class recovers the ambient category.",
            "A fully faithful subcategory containing a retract of each ambient object as\n"
            "a formal splitting recovers the ambient category by splitting exactly this class.",
        ),
    }
    with tarfile.open(bundle / "prior-review.tar.gz", "r:gz") as archive:
        manifest = archive.extractfile("SHA256SUMS").read()
        if hashlib.sha256(manifest).hexdigest() != PRIOR_SEAL:
            raise ValueError("earlier source review seal disagrees")
        for line in manifest.decode().splitlines():
            digest, name = line.split("  ", 1)
            if hashlib.sha256(archive.extractfile(name).read()).hexdigest() != digest:
                raise ValueError("earlier sealed file disagrees: " + name)
        previous = json.load(archive.extractfile("scope-at-review.json"))["modules"]
        for name in ("primary-reconstruction.md", "PCAObservations.lean"):
            if (bundle / name).read_bytes() != archive.extractfile(name).read():
                raise ValueError("the direct copy differs from the sealed archive: " + name)
    for name, row in previous.items():
        data = (repo / "Lean" / PACKAGE / (name + ".lean")).read_bytes()
        if name in edits:
            new, old = (text.encode() for text in edits[name])
            if data.count(new) != 1:
                raise ValueError("expected one changed docstring: " + name)
            data = data.replace(new, old, 1)
        if hashlib.sha256(data).hexdigest() != row["source_sha256"]:
            raise ValueError("differences outside the identified docstrings: " + name)
    return {
        "earlier_seal_sha256": PRIOR_SEAL,
        "unchanged_prior_modules": sorted(previous.keys() - edits.keys()),
        "docstrings_changed": sorted(edits),
        "added_modules": sorted(current.keys() - previous.keys()),
    }


def describe_export(path, target_names):
    names = {0: ""}
    roots = set()
    axioms = set()
    counts = {}
    with path.open("rb") as stream:
        for line in stream:
            row = json.loads(line)
            if "in" in row:
                part = row["str"] if "str" in row else row["num"]
                prefix = names[part["pre"]]
                leaf = str(part.get("str", part.get("i")))
                names[row["in"]] = prefix + "." + leaf if prefix else leaf
            for key in ("axiom", "def", "opaque", "thm", "quot", "inductive"):
                if key not in row:
                    continue
                counts[key] = counts.get(key, 0) + 1
                if key == "inductive":
                    continue
                name = names[row[key]["name"]]
                if key == "axiom":
                    axioms.add(name)
                if key == "thm" and name in target_names:
                    roots.add(name)
    if roots != set(target_names):
        raise ValueError("exported theorem roots differ: " + repr(roots ^ set(target_names)))
    if not axioms <= ALLOWED_AXIOMS:
        raise ValueError("unexpected axioms: " + repr(axioms - ALLOWED_AXIOMS))
    return {
        "sha256": sha(path), "bytes": path.stat().st_size, "records_by_declaration_kind": counts,
        "axioms": sorted(axioms), "theorem_roots": sorted(roots),
    }


def replay(repo, export_gzip=None):
    root = repo.resolve()
    if checked_output(["git", "rev-parse", "HEAD"], root).decode().strip() != PIN:
        raise ValueError("the checkout must be at " + PIN)
    lean = root / "Lean"
    sources = sources_and_objects(root)
    history = verify_history(root, sources)
    independent = json.loads((bundle / "independent-build.json").read_bytes())["modules"]
    if {r["module"] for r in independent} != PCA_MODULES or any(
        r["exit_code"] or r["source_sha256"] != sources[r["module"]]["source_sha256"]
        for r in independent
    ):
        raise ValueError("the independent compilation record has different source inputs")
    matching_objects = sorted(
        r["module"] for r in independent if r["olean_sha256"] == sources[r["module"]]["olean_sha256"]
    )
    tool_dir = Path(checked_output(["elan", "which", "lean"], lean).decode().strip()).parent
    clean_env = {k: v for k, v in os.environ.items() if k not in {"LEAN_PATH", "LEAN_SYSROOT"}}
    lake_path = checked_output(
        ["lake", "env", "printenv", "LEAN_PATH"], lean, clean_env
    ).decode().strip()
    search_roots = [lean / part for part in lake_path.split(os.pathsep) if part]
    for module in sources:
        relative = Path(PACKAGE) / (module + ".olean")
        actual = next((folder / relative for folder in search_roots if (folder / relative).is_file()), None)
        if actual is None or actual.resolve() != (lean / ".lake/build/lib/lean" / relative).resolve():
            raise ValueError("the selected project module is outside the tested checkout: " + module)
    names = [name for source in PROBES
             for name in declarations(bundle / (source + ".lean"), "IndependentPCAReading.")]
    names += declarations(lean / PACKAGE / "V46ComputableTuringCategoryChecks.lean", CHECK_NAMESPACE)
    if len(names) != 19 or len(set(names)) != 19:
        raise ValueError("expected twelve independent tests and seven committed statement checks")
    records = []
    with tempfile.TemporaryDirectory(prefix="cei-v81-citation-") as temporary:
        work = Path(temporary)
        env = dict(os.environ, LEAN_NUM_THREADS="1", LEAN_SYSROOT=str(tool_dir.parent),
                   LEAN_PATH=str(work) + os.pathsep + lake_path,
                   PATH=str(tool_dir) + os.pathsep + os.environ["PATH"])
        aliases = {str(bundle): "$BUNDLE", str(work): "$TMP", str(root): "$REPO"}

        def record(binary, args, output=None):
            argv = [str(tool_dir / binary), *map(str, args)]
            proc = subprocess.run(argv, cwd=lean, env=env, stdout=output or subprocess.PIPE,
                                  stderr=subprocess.PIPE)
            log = ((proc.stdout or b"") + proc.stderr).decode(errors="replace")
            public_args = [binary, *argv[1:]]
            for old, new in aliases.items():
                public_args = [arg.replace(old, new) for arg in public_args]
                log = log.replace(old, new)
            records.append({"argv": public_args, "exit_code": proc.returncode, "output": log})
            if proc.returncode:
                raise RuntimeError(json.dumps(records[-1], indent=2))
            return log

        opts = ["--threads=1", "--memory=1700", "-DwarningAsError=true"]
        for source in ("V46ComputablePowerInclusion", "V46ComputableTuringCategoryChecks"):
            record("lean", [*opts, PACKAGE + "/" + source + ".lean"])
        for source in PROBES:
            record("lean", [*opts, "-R", bundle, "-o", work / (source + ".olean"),
                            bundle / (source + ".lean")])
        export = work / "proofs.ndjson"
        with export.open("wb") as stream:
            record("leanexport", [*PROBES, CHECKS, "--", *names], output=stream)
        closure = describe_export(export, names)
        result = record("leanchecker", ["--from-export", export])
        if "Lean default kernel accepts the solution" not in result:
            raise ValueError("the kernel acceptance message is missing")
        if export_gzip is not None:
            with export.open("rb") as source, export_gzip.open("wb") as destination:
                with gzip.GzipFile(filename="", mode="wb", fileobj=destination, mtime=0) as zipped:
                    shutil.copyfileobj(source, zipped)
            closure["gzip_sha256"] = sha(export_gzip)
            closure["gzip_bytes"] = export_gzip.stat().st_size
    if sources != sources_and_objects(root):
        raise ValueError("module inputs changed during replay")
    return {
        "tested_commit": PIN,
        "checked_at_utc": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "toolchain": (lean / "lean-toolchain").read_text().strip(),
        "project_olean_source": "tested checkout's Lean/.lake/build/lib/lean",
        "history": history,
        "official_objects_matching_independent_compilation": matching_objects,
        "modules": sources, "probes": {name: sha(bundle / (name + ".lean")) for name in PROBES},
        "working_directory": "$REPO/Lean", "commands": records, "export": closure,
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("repo", type=Path, help="built repository checkout at the tested commit")
    parser.add_argument("--export-gzip", type=Path, help="save the kernel-accepted proof export")
    arguments = parser.parse_args()
    print(json.dumps(replay(arguments.repo, arguments.export_gzip), indent=2))
