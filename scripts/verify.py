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
    "CategoricalEssentialIncompleteness.PresentationLemmas.image_copair",
    "CategoricalEssentialIncompleteness.PresentationLemmas.pullback_le_iff",
    "CategoricalEssentialIncompleteness.PresentationLemmas.mono_copair_iff",
    "CategoricalEssentialIncompleteness.BooleanPresentation.consistent_iff_mono",
    "CategoricalEssentialIncompleteness.BooleanPresentation.complete_iff_regularEpi",
    "CategoricalEssentialIncompleteness.BooleanPresentation.consistent_complete_iff_isIso",
    "CategoricalEssentialIncompleteness.boolean_quotient_boundCopair_not_regularEpi",
    "CategoricalEssentialIncompleteness.Two.fibersIsColimit",
    "CategoricalEssentialIncompleteness.SubobjectPartition.cover_isIso",
    "CategoricalEssentialIncompleteness.SubobjectPartition.characteristic_isPullback",
    "CategoricalEssentialIncompleteness.SubobjectPartition.characteristic_positive",
    "CategoricalEssentialIncompleteness.SubobjectPartition.characteristic_negative",
    "CategoricalEssentialIncompleteness.SubobjectPartition.characteristic_unique_of_fibers",
    "CategoricalEssentialIncompleteness.boundFiber_mono_postcomp",
    "CategoricalEssentialIncompleteness.twoBooleanObject",
    "CategoricalEssentialIncompleteness.BooleanObject.boundMorphism",
    "CategoricalEssentialIncompleteness.BooleanMorphism.toTwo_isSplitEpi",
    "CategoricalEssentialIncompleteness.complete_extensions_and_decisions",
    "CategoricalEssentialIncompleteness.PredicateEmbedding.subobjectMap",
    "CategoricalEssentialIncompleteness.PredicateEmbedding.complete_extensions_and_decisions",
    "CategoricalEssentialIncompleteness.no_represented_boolean_decision",
    "CategoricalEssentialIncompleteness.InternalLattice.complement_isCompl",
    "CategoricalEssentialIncompleteness.InternalLattice.liftComplement_pair",
    "CategoricalEssentialIncompleteness.InternalHom.comp_pair",
    "CategoricalEssentialIncompleteness.InternalPredicateEmbedding.injective",
    "CategoricalEssentialIncompleteness.InternalDiagonalData.pairing_row",
    "CategoricalEssentialIncompleteness.InternalDiagonalData.diagonal_collapse",
    "CategoricalEssentialIncompleteness.InternalDiagonalData.RepresentationSection.represents",
    "CategoricalEssentialIncompleteness.InternalDiagonalData.representation_section_iff",
    "CategoricalEssentialIncompleteness.InternalDiagonalData.separatorPair_separates",
    "CategoricalEssentialIncompleteness.InternalDiagonalData.liftSeparator",
    "CategoricalEssentialIncompleteness.InternalDiagonalData.separator_represented",
    "CategoricalEssentialIncompleteness.InternalDiagonalData.separator_bounds_eq",
    "CategoricalEssentialIncompleteness.InternalDiagonalData.internal_inseparability",
    "CategoricalEssentialIncompleteness.InternalDiagonalData.no_global_separator",
    "CategoricalEssentialIncompleteness.InternalDiagonalData.separatorIsInitial",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.parameterizedRestriction",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.restrict_restrict",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.domainPointsEquiv",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.totalPointsEquiv",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.Products.restrict_pair",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.Products.pair_total",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.totalHom",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.totalHom_cartesian",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.domainAction_apply",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.precomp_domainInverse",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.domainInverse_comp",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.domain_le_iff",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.domain_bounds_ne",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.domainInverse_inf",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.domainInverse_top",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.domainInverse_bot",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.domainPredicates",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.enriched_internal_inseparability",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.enriched_no_global_separator",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.enriched_boolean_quotient_incomplete",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.enriched_boundCopair_not_regularEpi",
    "CategoricalEssentialIncompleteness.InternalHom.globalBinaryFanIsLimit",
    "CategoricalEssentialIncompleteness.InternalHom.globalProductIso_naturality",
    "CategoricalEssentialIncompleteness.InternalPredicates.globalPredicates",
    "CategoricalEssentialIncompleteness.InternalPredicateEmbedding.globalEmbedding",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.globalTotalEquivalence",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.globalTotalHasBinaryProducts",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.globalTotalPreservesBinaryProducts",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.parameterizedZeroMorphisms",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.global_nontrivial_iff",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.globalDomainEquiv",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.globalDomain_idem",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.globalDomainInverse_comparison",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.globalDomainOrderIso",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.globalDomain_le_iff",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.globalDomain_inf_hom",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.globalDomain_top_hom",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.globalDomain_bot_hom",
    "CategoricalEssentialIncompleteness.InternalDiagonalData.global_represents_iff",
    "CategoricalEssentialIncompleteness.InternalDiagonalData.global_representation",
    "CategoricalEssentialIncompleteness.InternalDiagonalData.global_inseparable",
    "CategoricalEssentialIncompleteness.PredicateLattice.presheaf",
    "CategoricalEssentialIncompleteness.SubobjectIdentification.presheafIso",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.predicatesOnTotals",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.domainSubobject",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.domainSubobject_injective",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.domainSubobject_naturality",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.global_complete_extensions_and_decisions",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.categorical_essential_incompleteness",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.categorical_boundCopair_not_regularEpi",
    "CategoricalEssentialIncompleteness.EnrichedRestriction.global_no_boolean_decision",
    "CategoricalEssentialIncompleteness.supportIdentity_partrec",
    "CategoricalEssentialIncompleteness.Numerical.numericalCategory",
    "CategoricalEssentialIncompleteness.Numerical.numericalRestriction",
    "CategoricalEssentialIncompleteness.Numerical.total_iff",
    "CategoricalEssentialIncompleteness.Numerical.numericalZeroMorphisms",
    "CategoricalEssentialIncompleteness.Numerical.restrict_zero",
    "CategoricalEssentialIncompleteness.Numerical.nat_nontrivial",
    "CategoricalEssentialIncompleteness.re_inter",
    "CategoricalEssentialIncompleteness.re_union",
    "CategoricalEssentialIncompleteness.Numerical.domainSupportOrderIso",
    "CategoricalEssentialIncompleteness.Numerical.Domain.le_iff",
    "CategoricalEssentialIncompleteness.Numerical.Domain.inf_hom",
    "CategoricalEssentialIncompleteness.Numerical.Domain.top_hom",
    "CategoricalEssentialIncompleteness.Numerical.Domain.bot_hom",
    "CategoricalEssentialIncompleteness.Numerical.domainInverse_support",
    "CategoricalEssentialIncompleteness.Numerical.complementary_support_recursive",
    "CategoricalEssentialIncompleteness.Numerical.recursive_iff_complemented_support",
    "CategoricalEssentialIncompleteness.NumericalPER.perCategory",
    "CategoricalEssentialIncompleteness.NumericalPER.ofRepresentative_eq_iff",
    "CategoricalEssentialIncompleteness.NumericalPER.discrete_arrow_eq_iff",
    "CategoricalEssentialIncompleteness.Numerical.toPER",
    "CategoricalEssentialIncompleteness.Numerical.toPER_faithful",
    "CategoricalEssentialIncompleteness.Numerical.toPER_full",
    "CategoricalEssentialIncompleteness.Numerical.ofDiscreteRepresentative_total",
    "CategoricalEssentialIncompleteness.Numerical.natFunction_computable",
    "CategoricalEssentialIncompleteness.Numerical.natArrow_natFunction",
    "CategoricalEssentialIncompleteness.NumericalPER.inclusion_mono",
    "CategoricalEssentialIncompleteness.NumericalPER.supportSubobject_le_iff",
    "CategoricalEssentialIncompleteness.NumericalPER.supportSubobject_eq_iff",
    "CategoricalEssentialIncompleteness.NumericalPER.inverse_isPullback",
    "CategoricalEssentialIncompleteness.Numerical.domainSubobject",
    "CategoricalEssentialIncompleteness.Numerical.supportSubobject_in_range_iff",
    "CategoricalEssentialIncompleteness.Numerical.domainInverse_support_comparison",
    "CategoricalEssentialIncompleteness.NumericalPER.enumerable_union_lift",
    "CategoricalEssentialIncompleteness.NumericalPER.enumerable_union_isLUB",
    "CategoricalEssentialIncompleteness.Numerical.complementary_support_compl",
    "CategoricalEssentialIncompleteness.Numerical.separatesSupports_iff",
    "CategoricalEssentialIncompleteness.Numerical.exists_separator_iff",
    "CategoricalEssentialIncompleteness.Numerical.no_separator_iff_recursively_inseparable",
    "CategoricalEssentialIncompleteness.NumericalPER.pair_fst",
    "CategoricalEssentialIncompleteness.NumericalPER.pair_snd",
    "CategoricalEssentialIncompleteness.NumericalPER.product_hom_ext",
    "CategoricalEssentialIncompleteness.NumericalPER.productIsLimit",
    "CategoricalEssentialIncompleteness.NumericalPER.perHasBinaryProducts",
    "CategoricalEssentialIncompleteness.NumericalPER.relationIso",
    "CategoricalEssentialIncompleteness.Numerical.product",
    "CategoricalEssentialIncompleteness.Numerical.productIso",
    "CategoricalEssentialIncompleteness.Numerical.productIso_hom_fst",
    "CategoricalEssentialIncompleteness.Numerical.productIso_hom_snd",
    "CategoricalEssentialIncompleteness.Numerical.productMapIsLimit",
    "CategoricalEssentialIncompleteness.Numerical.productIsLimit",
    "CategoricalEssentialIncompleteness.Numerical.totalHasBinaryProducts",
    "CategoricalEssentialIncompleteness.Numerical.toPER_preservesBinaryProducts",
    "CategoricalEssentialIncompleteness.NumericalPER.unitIsTerminal",
    "CategoricalEssentialIncompleteness.NumericalPER.subsetInclusion_mono",
    "CategoricalEssentialIncompleteness.NumericalPER.equalizer_condition",
    "CategoricalEssentialIncompleteness.NumericalPER.equalizer_existsUnique",
    "CategoricalEssentialIncompleteness.NumericalPER.equalizerIsLimit",
    "CategoricalEssentialIncompleteness.NumericalPER.perHasFiniteLimits",
    "CategoricalEssentialIncompleteness.NumericalPER.relationRegularEpi",
    "CategoricalEssentialIncompleteness.NumericalPER.imageQuotient_regularEpi",
    "CategoricalEssentialIncompleteness.NumericalPER.imageInclusion_mono",
    "CategoricalEssentialIncompleteness.NumericalPER.image_factorization",
    "CategoricalEssentialIncompleteness.NumericalPER.imageFactorisation",
    "CategoricalEssentialIncompleteness.NumericalPER.perHasStrongEpiMonoFactorisations",
    "CategoricalEssentialIncompleteness.NumericalPER.hasCoequalizer_of_isKernelPair",
    "CategoricalEssentialIncompleteness.NumericalPER.pullbackPER_support",
    "CategoricalEssentialIncompleteness.NumericalPER.pullback_condition",
    "CategoricalEssentialIncompleteness.NumericalPER.pullback_hom_ext",
    "CategoricalEssentialIncompleteness.NumericalPER.pullbackIsLimit",
    "CategoricalEssentialIncompleteness.NumericalPER.pullback_isPullback",
    "CategoricalEssentialIncompleteness.NumericalPER.imageInclusion_isIso",
    "CategoricalEssentialIncompleteness.NumericalPER.regularEpi_of_image_section",
    "CategoricalEssentialIncompleteness.NumericalPER.image_section_output",
    "CategoricalEssentialIncompleteness.NumericalPER.pullbackPreimageFunction_supported",
    "CategoricalEssentialIncompleteness.NumericalPER.pullbackImageSection_fac",
    "CategoricalEssentialIncompleteness.NumericalPER.pullbackSnd_regularEpi",
    "CategoricalEssentialIncompleteness.NumericalPER.perRegular",
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

        manuscript = json.loads((ROOT / "MANUSCRIPT_SOURCE.json").read_text())
        manuscript_files = []
        for record in manuscript["files"]:
            expected = record["git_blob"]
            patch = patch_by_path.get(record["path"])
            if patch:
                if patch["source_git_blob"] != expected:
                    raise RuntimeError("Manuscript provenance mismatch: " + record["path"])
                expected = patch["patched_git_blob"]
            actual = git_blob((ROOT / record["path"]).read_bytes())
            if actual != expected:
                raise RuntimeError("Manuscript differs from its recorded hash: " + record["path"])
            manuscript_files.append({"path": record["path"], "expected": expected,
                                     "actual": actual})
        report["manuscript_files"] = manuscript_files

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
