# WSL2 assignment for the v66 Lean writing review

Work in `/home/flengyel/src/CategoricalEssentialIncompleteness`. Fetch `origin` and start from the latest private `origin/main`. Preserve local work and concurrent changes. Read `AGENTS.md`, `MANUSCRIPT_CURRENT.json`, the [v66 correspondence](../FORMALIZATION_STATUS_V66.md) and the [v65 sentence review](reviews/V65_SENTENCES_2026-11-18/review.md).

## Apply the reviewed edits

Apply the [prose patch](reviews/V66_PALOMAR_LEAN_PROSE.patch) from the repository root. These seven files had identical Git blobs at the tested candidate `e2168b55b1c7e3a291c39ad1e5c613a780406f0a` and at `cb9637f99092a2e14cfd50bbd5570cf6cd3cf963` on main.

```sh
git apply --check docs/reviews/V66_PALOMAR_LEAN_PROSE.patch
git apply docs/reviews/V66_PALOMAR_LEAN_PROSE.patch
git diff --check
```

The patch revises 37 of 50 documentation blocks. The forward application reproduced the reviewed sources byte for byte. All text between the documentation blocks matched the original files, including declarations, proofs, and the license headers. If a file has since changed, compare its current statement and apply the appropriate wording to that revision. If the edits are already present, continue with the remaining files.

| Reviewed modules | Mathematical content |
| --- | --- |
| `CEIPalomar.Challenge`, `CEIPalomar.CalculusDefinitions` | The atomic sentence morphism, signed theories, refutation by inverse image, and disjointness of theorem and refutation subobjects. |
| `CEIPalomar.Solution`, `CEIPalomar.ManuscriptChecks` | The restriction-idempotent form of Corollary 4.8, the closed extensions in the same language, and the diagonal pair in the predicate category of Peano arithmetic. |
| `V46ArithmeticSignedContradiction`, `V46ArithmeticSignedConsistency`, `V46ArithmeticSignedGeneration` | Internal derivations in every model of PA, the conclusion morphism on formulas and sentences, and the two direct images whose join generates the signed theory. |

For example, `boolean_assignment` quantifies over an assignment, then a theory, then every pair of subobjects on which the assignment has the prescribed values. Its docstring records that one theory contains all those signed theories. In `no_contradictory_derivations`, “internal” specifies the derivations quantified over in each model of PA. “Actual” contributed no hypothesis.

## Review the project’s Lean sources

1. Inventory the tracked `.lean` files. Read the project-owned sources in `Lean/CategoricalEssentialIncompleteness/`, its umbrella module, `Lean/CEIPalomar/`, and project-owned checks and scripts. Use `SOURCE_PINS.json` and `LOCAL_PATCHES.json` to distinguish project contributions from upstream copies. Where a generated file contains project prose, correct its source. Record the files reviewed and edited so the extent of the review can be checked.
2. Check module headings, docstrings, ordinary comments and names of definitions, lemmas, structures and fields against the declarations and the corresponding manuscript sections. Use terminology established in the paper, the literature or Mathlib. Give a definition at first use if the paper introduces a concept. Remove descriptions of drafting or verification from proof commentary. Keep comments that explain a mathematical step or an implementation constraint a maintainer needs to know. Use word searches to find passages, then read each passage in context. Follow Knuth, Larrabee and Roberts on self-contained statements and unnecessary jargon. [*Mathematical Writing*, §1](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf)
3. Distinguish a mathematical qualification from an editorial one. “Regular image,” “internal derivation,” “standard model,” and “closed extension in the same language” can change the assertion. Where “actual,” “native,” “literal,” or “printed” occurs, identify the object or distinction intended. In particular, review `ofNative`, `native_inseparable_iff`, `native_essential_iff`, and `printed_corollary`. Where a name obscures the mathematics, use the presentation, relation or corollary it expresses. Check callers, existing public interfaces, links, and the names in `Lean/comparator.json` before changing an identifier. Keep compatible public entry points. Commit any identifier changes separately from prose edits so each can be checked.
4. Check each replacement against the Lean type. Preserve the direction of each morphism and the order of quantifiers. For Corollary 4.8, use subobjects of the index object and pullback along the atomic sentence morphism. Distinguish the general categorical proof, the PA predicate category, and interpretation in the standard model wherever all three occur. Keep the package docs and registry descriptions consistent with the statements they accompany.

## Verify and push

Use the repository’s pinned toolchain and the commands in the [private preparation report](V66_PALOMAR_PREPARATION_REPORT.md). Compare the prose-only diff with the baseline to verify that all text outside comments is identical. For renamed declarations, check all dependent modules and update references. Run the affected manuscript and axiom audits, the Challenge import and placeholder audit, and the expected-type and proof checks in `CEIPalomar.ManuscriptChecks`. Run the private Comparator workflow on the revised candidate and record the verdicts of Comparator, Lean’s default kernel, NanoDa, and con-ron against its exact SHA. The earlier private run `44856537123` certifies its own source commit.

Commit the edited Lean sources and `docs/V66_LEAN_WRITING_REPORT.md` to private `origin/main`. Include the review scope, any retained names that required a decision, the full tested SHA, the commands and results, and the private run link in the report. Push without force and fetch again. Verify that remote `main` contains the tested commit, that the tested package files match byte for byte, and that `MANUSCRIPT_CURRENT.json` selects v66. Return the full tested and remote SHAs and the report link. If a check blocks completion, push the verified progress and identify the failing command or exact unresolved declaration. Official Palomar submission and publication require a separate author decision.
