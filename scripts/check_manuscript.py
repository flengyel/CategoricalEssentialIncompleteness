"""Check that Lean's recorded target is the current manuscript and its artifacts."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import zipfile


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def repository_path(root: Path, name: str) -> Path:
    path = (root / name).resolve()
    if Path(name).is_absolute() or not path.is_relative_to(root.resolve()):
        raise RuntimeError("Manuscript path leaves the repository: " + name)
    return path


def read_target(root: Path) -> dict:
    target = json.loads((root / "MANUSCRIPT_CURRENT.json").read_text())
    if type(target.get("version")) is not int or target["version"] < 1:
        raise RuntimeError("Current manuscript version must be a positive integer")
    for key in ("entry_point", "pdf", "source_archive", "correspondence",
                "statement_audit", "axiom_audit", "production_prefix", "audit_marker"):
        if not isinstance(target.get(key), str) or not target[key]:
            raise RuntimeError("Missing current manuscript field: " + key)
    if not isinstance(target.get("files"), list) or not target["files"]:
        raise RuntimeError("Current manuscript file manifest is empty")
    return target


def manuscript_paths(root: Path, target: dict) -> list[Path]:
    names = ["MANUSCRIPT_CURRENT.json", target["correspondence"],
             *(record["path"] for record in target["files"])]
    return [repository_path(root, name) for name in sorted(set(names))]


def check_manuscript(root: Path) -> dict:
    root = root.resolve()
    target = read_target(root)
    version = target["version"]
    entry = repository_path(root, target["entry_point"])
    source_root = entry.parent
    preamble = source_root / "preamble.tex"
    preamble_text = re.sub(r"(?<!\\)%[^\n]*", "", preamble.read_text())
    versions = re.findall(r"\bVersion\s+(\d+)\b", preamble_text)
    if not versions or set(versions) != {str(version)}:
        raise RuntimeError("Current manuscript version disagrees with preamble.tex")
    lines = repository_path(root, target["correspondence"]).read_text().splitlines()
    heading = lines[0] if lines else ""
    if not re.search(r"\bmanuscript v" + str(version) + r"\b", heading):
        raise RuntimeError("Current correspondence table targets a different manuscript version")
    if not target["pdf"].endswith(f"_v{version}.pdf"):
        raise RuntimeError("Current PDF filename does not identify the target version")
    if not target["source_archive"].endswith(f"_v{version}_source.zip"):
        raise RuntimeError("Current source archive filename does not identify the target version")

    records = {}
    for record in target["files"]:
        name = record["path"]
        if name in records:
            raise RuntimeError("Duplicate current manuscript record: " + name)
        records[name] = record
        data = repository_path(root, name).read_bytes()
        if (git_blob(data) != record["git_blob"] or
                hashlib.sha256(data).hexdigest() != record["sha256"] or
                len(data) != record["size"]):
            raise RuntimeError("Current manuscript differs from its recorded hash or size: " + name)

    reachable = set()
    pending = [entry]
    while pending:
        path = pending.pop()
        name = str(path.relative_to(root))
        if name in reachable:
            continue
        reachable.add(name)
        text = re.sub(r"(?<!\\)%[^\n]*", "", path.read_text())
        for include in re.findall(r"\\(?:input|include)\s*\{([^}]+)\}", text):
            if not include.endswith(".tex"):
                include += ".tex"
            child = (source_root / include).resolve()
            if not child.is_relative_to(source_root.resolve()):
                raise RuntimeError("TeX input leaves the current source directory: " + include)
            pending.append(child)
    recorded_tex = {name for name in records if name.endswith(".tex")}
    physical_tex = {str(path.relative_to(root)) for path in source_root.rglob("*.tex")}
    if reachable != recorded_tex or reachable != physical_tex:
        raise RuntimeError("Current TeX input closure, manifest, and source directory differ: " +
                           repr(sorted((reachable ^ recorded_tex) | (reachable ^ physical_tex))))

    pdf = repository_path(root, target["pdf"])
    archive = repository_path(root, target["source_archive"])
    built_pdf = source_root / "main.pdf"
    for path in (pdf, archive, built_pdf):
        if str(path.relative_to(root)) not in records:
            raise RuntimeError("Current artifact is absent from the manifest: " + str(path))
    if built_pdf.read_bytes() != pdf.read_bytes():
        raise RuntimeError("Built PDF differs from the current versioned PDF")

    expected_members = {"latex/" + str(repository_path(root, name).relative_to(source_root)): name
                        for name in reachable}
    with zipfile.ZipFile(archive) as package:
        names = package.namelist()
        if len(names) != len(set(names)):
            raise RuntimeError("Duplicate source archive member")
        archived_tex = {name for name in names if name.endswith(".tex")}
        if archived_tex != set(expected_members):
            raise RuntimeError("Current source archive has a different TeX inventory")
        for member, name in expected_members.items():
            if package.read(member) != repository_path(root, name).read_bytes():
                raise RuntimeError("Current source archive differs from TeX source: " + name)

    for key in ("statement_audit", "axiom_audit"):
        name = target[key]
        if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)+", name):
            raise RuntimeError("Invalid current audit module: " + name)
        if not (root / "Lean" / (name.replace(".", "/") + ".lean")).is_file():
            raise RuntimeError("Missing current audit module: " + name)
    if not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)+",
                        target["production_prefix"]):
        raise RuntimeError("Invalid current production-module prefix")

    return {"version": version, "entry_point": target["entry_point"],
            "correspondence": target["correspondence"],
            "files_verified": sorted(records), "tex_files": len(reachable),
            "source_archive_matches": True, "pdf_copy_matches": True,
            "sha256": {str(path.relative_to(root)): hashlib.sha256(path.read_bytes()).hexdigest()
                       for path in manuscript_paths(root, target)}}
