# V46 continuation — 3 November 2026

This continuation constructs the generic partial-map interpretation, the
regular extensive syntactic total category, regular model interpretations,
the actual arithmetic-ultrapower comparison, named substitution and all seven
logical schemes. It also proves the unary and canonical tagged parts of the
finite-membership lemma and restriction preservation on the full Karoubi
envelope. **The full v46 formalization remains incomplete.**

The [correspondence table](../FORMALIZATION_STATUS_V46.md) retains all 62
numbered results, three definitions and required unnumbered constructions.
The [first batch](V46_IMPLEMENTATION_2026-11-03.md), including all four
Section 3 results, is preserved and reverified by the continued combined
entry point.

## Source and revision

- Existing WSL2 checkout: `/home/flengyel/src/CategoricalEssentialIncompleteness`;
  repository `flengyel/CategoricalEssentialIncompleteness`, branch `main`.
- Starting revision: `a5d369b3ce3ab161cdd5b87e530a182ea9787db9`.
- Implementation commit and remote confirmation: `bb32a4089f8f37d7dbc5745da0ecaad5eaa2aa4d` (ordinary push and remote-ref confirmation succeeded).
- Tested final source identity:
  `938d13139abe663c2d57d39a4de2700cc34cedf629f888019383a27e13c258c3`.
  The [verification record](V46_CONTINUATION_VERIFICATION_2026-11-03.json)
  records every input hash, command, exit status and transitive axiom set.
- Manuscript v46 remains at publication
  `558a20eed4c62d59eada05f5500cf233671078e9`, entry
  `manuscript/latex/main.tex`. No TeX, PDF, archive, source pin, dependency pin
  or toolchain was changed. The historical v5 table and reports are preserved.

There are 28 new production modules and 22 new statement-check modules.
Every completed production module is imported by the combined entry point,
and every statement-check module is reachable from `V46StatementAudit`.
The existing dynamic audit and verifier required no change for this batch.

## Results and effective hypotheses

Here `V46` abbreviates `CategoricalEssentialIncompleteness.V46`, and `LC`
abbreviates `CategoricalEssentialIncompleteness.LocalConnectedness`.

| Manuscript result or construction | Exact declarations and scope |
| --- | --- |
| Proposition 4.1 | `V46.PartialMaps.interpreted_theory`, `theory_subobject`, `range_totalValue`, `totalEquivalence`. The actual quotient of mono-left spans constructs `Par(D,Mono)` for arbitrary D with pullbacks; total maps recover D and restriction idempotents split. Regular D supplies image ranges. Canonical inverse spans of ordinary monomorphisms give the actual ordinary validity-subobject factorization and consistency implication. Target zero/coproduct structures remain data of the supplied range functor; they are not inferred from regularity alone. |
| Lemma 5.3 | `V46.SyntacticPredicates.predicateEquivalence`, `predicateRegular`, `totalSplitRegular`, `predicateFinitaryExtensive`, `totalSplitFinitaryExtensive`, `subobject_is_predicate_inclusion`, `totalSplit_mono_partial_inverse`. Objects are arbitrary Σ₁ predicates and arrows are T-provably supported, uniquely total Σ₁ graphs modulo T-provable equality. Only T extending PA is assumed. The equivalence, finite limits, represented images, regularity, disjoint stable finite coproducts and partial inverses of every total-split mono are constructed. No consistency or c.e. premise is introduced. |
| Lemma 5.4, achieved parts | `V46.FiniteSigmaOne.finite_membership_PA`, `witnessVector_exists`, `finite_tagged_membership_PA`, `selected_tagged_membership_PA`, `selectedTaggedList_model`, `pairTag_primrec`. Actual canonical witness vectors and bounded reads give PA equivalence for arbitrary unary Σ₁ entry conditions, including nonstandard lengths. Finite Π₁ tests and concrete primitive-recursive pair tags/payloads are implemented; the selected-case variant enforces valid-tag coverage. A generic primitive-recursive tag-reader to PA-Π₁ representation bridge remains open, so the full printed lemma retains pending status. |
| Proposition 6.4 | `V46.PredicateInterpretation.regular`, `total_regular`, `canonical_regular`, `recursive_regular`, `totalCanonicalComparison`, `recursiveDomainComparison`, `recursiveDomainFunctor_graph`. For arbitrary arithmetic M satisfying T, actual graph-defined functions preserve finite limits, finite coproducts and regular images. Natural comparisons recover literal domains of interpreted idempotents, including the original recursively interpreted product/coproduct carriers. Image isomorphisms commute with the inclusions into the actual interpreted codomain. |
| Lemma 6.7 | `V46.Ultrapower.functor`, `regular`, `subtypeEquiv`, `subtypeEquiv_naturality`, `regularImageIso_hom_ι`. For a proper ultrafilter on arbitrary I, the actual quotient functor preserves finite limits, finite coproducts and regular images, including empty carriers and predicates. |
| Lemma 6.8 | `V46.ArithmeticUltrapower.eval_representative`, `modelsPA`, `predicateComparison`, `comparison`, `canonicalComparison`, `recursiveComparison`. Arithmetic is constructed on the natural-number quotient; Łoś is proved for all arithmetic formulas, with unbounded quantifiers ranging over the whole quotient. The same-family predicate comparison is natural for every graph. The actual equivalence and domain/coding comparisons extend it to all total-split objects and morphisms of the original recursive interpretation. |
| Conditional soundness transport | `V46.Ultrapower.soundness_transport`, `conclusion_range_consistent`, `V46.ArithmeticUltrapower.canonical_soundness_transport`. Given standard validity, its proof-to-validity factor and semantic disjointness, the constructed arithmetic comparison yields the ultrapower factorization, monicity and consistent conclusion image. This does not construct the decoded standard soundness instance of 6.5–6.6, and does not complete Theorem 6.9. |
| Proposition A.3 | `V46.CategoricalSyntax.substitutionAlgebra`, `substitutionOriginalHom`, `substitutionFold_original`, `substitutionFold_unique`, `termSubstitution`, `formulaSubstitutionOption`, `admissibility_complemented`. The actual parameter-slice algebra retains original/result pairs; the equal-name quantifier branch returns the original body. Its original projection is proved an algebra morphism, so initiality gives the identity. The success pullback is complemented. Hypotheses are arbitrary regular finitary extensive D, internal decidable equality and the parameter-stable initial syntax/list algebras assumed in Definition A.1. |
| Theorem A.6 and list foundations | `V46.CategoricalSyntax.logicalAxioms`, `logicalRules`, `generated_firstOrder_theory`, and `V46.StableListAlgebra.membership_append`, `parameterFold_unique`. All seven logical scheme morphisms and their specified admissibility/absence parameter objects are constructed. For an initial algebra of the actual inference functor, the image is closed and least, contains logical/nonlogical axioms, and its sentence image is the required pullback. Membership of concatenation is proved by parameterized initiality. Concrete derivation initiality is not inferred from this conditional theorem. |
| Karoubi restriction and B.9 extension | `LC.V46.KaroubiRestriction.restriction`, `rst_f`, `toKaroubi_preserves`; `LC.EffectiveFork.Recursion.karoubiInclusion_preserves_restrictions`, `karoubiEquivalence_preserves_restrictions`. All four restriction axioms hold at arbitrary idempotents with underlying formula `e ≫ rst f`. The actual inclusion and previously constructed Karoubi equivalence preserve the restriction structure. |

The exact deterministic trace-presentation comparison of 5.1 remains separate
from results in the maintained production graph presentation. No numerical
computability argument is substituted for T-provable graph equality or
parameter-slice initiality.

## Verification

All Lean/Lake jobs used the project lock and `LEAN_NUM_THREADS=1`. Linux Elan
shims and the existing pinned project environment were retained.

| Run | Outcome and evidence |
| --- | --- |
| Reused starting baseline | The starting source snapshot was checked against the successful committed verification record: `480e9801a1eb107629bf1d65c903a3247a0a7768d997378de835d8afb469aa5b`. Its original baseline/final logs are preserved; no redundant unchanged baseline run was made. |
| Targeted implementation checks | Production and explicit statement modules were built and replayed with `lake env lean -DwarningAsError=true`. Principal evidence includes `.codex-work/v46-ultrapower/attempt-14-root-strict.log`, `.codex-work/v46-predicates/{core-images-strict,relations-limits-regular-strict}.log`, `.codex-work/v46-predicates-extensive/production-20261103T185036098095Z/`, `.codex-work/v46-finite-sigma1/production-build-strict.log`, and timestamped partial-map/model records. |
| First combined integration | `bash scripts/verify-wsl.sh`, exit 1. New imports followed a module documentation command in the combined entry file. They were moved into its opening import block; proof sources and pins were unchanged. Failure evidence: `.codex-work/verify-20261103T185237Z-XR0AHu/`. |
| Integrated category/model/substitution batch | Same command, exit 0; 90 commands, 1,274 retained and 1,857 v46 declarations in 46 production modules. Source identity `45ced6d091763d5ad9785ac4ab09af2ef667d2f4eeb4b076c1863020090b9a18`; evidence `.codex-work/verify-20261103T185431Z-cZWzEH/`. |
| Final integration after the finite-witness proof | `bash scripts/verify-wsl.sh`, exit 0; all 92 commands passed, with 1,274 retained declarations and all 1,937 v46 declarations in 47 production modules. Every source input was unchanged from start to finish. Evidence: `.codex-work/verify-20261103T191030Z-iEObtl/`. |

Toolchain: `leanprover/lean4:v4.35.0-rc2`, compiler
`11acb17ec6b07a8f9e9173e6845197929540936b`. Mathlib:
`065356127b1dc0016f66b7283ce0ce2c4055aa55`; Foundation:
`01f617fbe240a84aaf1c45b31b9d65e0a2e21c1d`. The verifier retains all 356
imported-source checks, historical manuscript checks, 24 v46 source/PDF/archive
checks and all 16 dependency revisions, the combined build, v5 and v46
statement audits, every strict v46 source replay and both axiom audits.
Only `propext`, `Quot.sound` and `Classical.choice` are permitted transitively.

The [hostile correspondence review](reviews/V46_CONTINUATION_REVIEW_2026-11-03.md)
records independent source inspections, scope findings and unresolved
applications. Its [source manifest](reviews/V46_CONTINUATION_SOURCE_SHA256.txt)
fixes all 28 new production files. No independent-kernel replay, registry
verification or new full-manuscript mathematical-writing review is claimed.

## Remaining obligations

The full target is open. The first major concrete construction is now
Proposition 5.5: Σ₁ finite evaluation records for arbitrary coefficient
algebras and every parameter P, with totality and unique output proved in T
by simultaneous node-count induction. The list and inference versions and
their concrete initiality/comparison proofs are also required.

Other outstanding work comprises the exact deterministic trace comparison;
the general primitive-recursive tag bridge; membership of deletion,
identity/absent-variable substitution and the quantified admissibility
identity; concrete named-variable/Craig/LK comparisons; standard decoded
semantic substitution and soundness; the partial proof-search lift and
categorical arithmetic chain; indexed theories, numeral fibers and uniform
independent sentences; numerical and representation-independent Miller
realizations; cosheaf slice inference initiality and general c.e.-axiom
closure; and the remaining family-coherence correspondence checks. The table
keeps these separate from the proved generic interfaces and preserved v5
results.

## Committed-byte delivery

The active Windows profile was queried as `C:\Users\fleng`. Its Downloads
known-folder registry setting is `%USERPROFILE%\Downloads`; the existing
WSL directory `/mnt/c/Users/fleng/Downloads` was checked. Final reports,
correspondence table and review are delivered from `git show` of the final
report commit into a dated, commit-suffixed CEI-v46 directory, preserving any
different existing material. `DELIVERY_SHA256.json` beside the copies records
that commit, actual destinations and byte-for-byte SHA-256 checks.
