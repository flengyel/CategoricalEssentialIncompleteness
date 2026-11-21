# Lean writing review for manuscript v66

The reviewed source is `a65aeb4d5aae48ef9d71bd3352f8935e7612e434`. The Palomar comparison covers Corollary 4.8, the Boolean assignment used in its proof, and the existence consequence of Lemma 8.9. Comparator compares three theorem declarations and the auxiliary definition `CEIPalomar.IsNullaryCalculus`. The manuscript guide covers all 77 numbered results. [Tested package](https://github.com/flengyel/CategoricalEssentialIncompleteness/tree/a65aeb4d5aae48ef9d71bd3352f8935e7612e434/Lean/CEIPalomar) · [Comparator configuration](../Lean/comparator.json) · [Guide](LEAN_GUIDE_V66.md)

## Scope

The inventory lists all 2,568 tracked Lean files. It distinguishes the project's modules, umbrella import, Palomar package and Challenge audit from sources identified in `SOURCE_PINS.json`. For each pinned file, the comparison uses the Git blob at its recorded upstream revision. A block counts as revised if its comment text changed. The last column records changes to Lean text outside comments. [File inventory](reviews/V66_LEAN_WRITING_INVENTORY.tsv) · [Source pins](../SOURCE_PINS.json) · [Local patches](../LOCAL_PATCHES.json)

| Source | Files | Prose blocks reviewed | Files edited | Blocks revised |
| --- | ---: | ---: | ---: | ---: |
| Project | 2,214 | 5,811 | 1,541 | 2,741 |
| Pinned files with local prose changes | 17 | 26 | 3 | 3 |
| Other pinned files | 337 | 0 | 0 | 0 |

The review covered module and section headings, documentation on declarations and fields, ordinary comments, and the names used in statements and their callers. The finite syntax, PA interpretations, Miller sequence and three-point space developments use distinct representations. Their documentation now identifies, for example, substitution on named formulas, primitive recursiveness on the standard natural numbers, and initiality in a parameter slice. The one-time module port supplied filename headings. The tracked Lean modules contain the maintained text. The three edits to pinned files concern locally added headings, including one inside a nested comment. [Named substitution](../Lean/CategoricalEssentialIncompleteness/V46MillerNamedProofImageNativeFormulaSubstitutionComparison.lean) · [Trace predicate](../Lean/CategoricalEssentialIncompleteness/V46UniformTracePrimitiveCoding.lean) · [Fork formula algebra](../Lean/CategoricalEssentialIncompleteness/V46CanonicalFormulaStabilityChecks.lean)

References to the arithmetic diagonal, proof search and Miller cut reduction now use Lemmas 8.1, 8.2 and 9.3 of v66. Comments that described completed clauses as further obligations now specify the constructions established in the cited modules. Qualifications such as *regular image*, *internal derivation* and *standard model* distinguish the image, the proof object or the interpretation used in the statement. Equality of raw words can retain binder names even when translated formulas are provably equivalent. The review used the v66 correspondence, the earlier sentence review, and the advice on hypotheses, notation and jargon in §1 of Knuth, Larrabee and Roberts. [Correspondence](../FORMALIZATION_STATUS_V66.md) · [Sentence review](reviews/V65_SENTENCES_2026-11-18/review.md) · [Mathematical Writing](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf)

Web GPT's patch changed 37 of 50 documentation blocks in seven files. Applying it to `290c06730275c2ec740e26f770f057db036d8ebd` reproduced all seven reviewed blobs. For each prose commit, a Lean comment scanner compared all bytes outside comments, including whitespace and license headers. It accounted for nested comments, strings and quoted identifiers. The comparisons found no differences. Across the entire review, only `Solution.lean` and `ManuscriptChecks.lean` changed outside comments, in the naming commit. A subsequent formatting commit wrapped five lines in those files. Comparing the whitespace-separated tokens confirmed that every token was preserved. All 166 Lean line links in the guide were checked against their source lines, and 16 were adjusted. [Reviewed patch](reviews/V66_PALOMAR_LEAN_PROSE.patch) · [Patch commit](https://github.com/flengyel/CategoricalEssentialIncompleteness/commit/9ecad203ef96ea45981b620d9034c7a420d1c80b) · [Wider review](https://github.com/flengyel/CategoricalEssentialIncompleteness/commit/95e5cf7a8492f0d1c68e9a3c171a88c0d375c32f) · [Names](https://github.com/flengyel/CategoricalEssentialIncompleteness/commit/ef51050148473b09c5043f72645297d16fc3f1fd)

## The presentation and the equivalences

| Preferred declaration | Compatible entry point | Mathematical content |
| --- | --- | --- |
| `ofNullaryPresentation` | `ofNative` | Gives the import-limited calculus at `X` from a family of nullary first-order presentations. Its fields are the given syntax, inference and initial derivation algebras. |
| `subobjectInseparable_iff_inseparable` | `native_inseparable_iff` | Identifies a separator given by a complementary partition with a pair of complementary subobjects satisfying the same two inequalities. |
| `essentiallyIncomplete_signedTheory_iff` | `native_essential_iff` | Identifies the two statements about the signed theory. A closed extension is a sentence subobject together with a proof that it is fixed by generation. |
| `ManuscriptChecks.essentiallyIncomplete_iff_inseparable_domains` | `ManuscriptChecks.printed_corollary` | Specializes the exported equivalence to the total category and applies `RestrictionSubobjects.inseparable_iff` to the two domains. |

Lean checked definitional equality of the type and value of each public entry point with its preferred declaration. A separate client also compiled the restriction-splitting specialization through the former name. The compared declarations retain their original names. `Calculus.consistent` describes disjointness from the inverse image under sentence negation, and `IsNullaryCalculus` states the presentation hypothesis. For each family satisfying the hypotheses of Theorem 4.7, `isNullaryCalculus_of_data` supplies the witness. Stable implementation names such as `PrintedObjectCoding` and the `V46` module prefix continue to identify objects used by existing imports and the guide. [Solution](../Lean/CEIPalomar/Solution.lean) · [Manuscript checks](../Lean/CEIPalomar/ManuscriptChecks.lean)

For disjoint subobjects `a,b` of `X` with consistent generated signed theory, a complete consistent closed extension would give complementary theorem and refutation subobjects. Pullback along the atomic sentence morphism would separate `a` and `b`. Conversely, a separator gives a Boolean assignment. That assignment determines **one** closed, consistent, complete theory containing the signed theory of **every** pair on which it takes the prescribed values. Essential incompleteness quantifies over every consistent closed internal extension in the same language. In the predicate category of PA, the diagonal subobjects of the number object supply the witness for Lemma 8.9. The general proof uses subobjects and morphisms throughout. [Challenge](../Lean/CEIPalomar/Challenge.lean) · [Registry entry](../Lean/formalization.yaml)

## Verification

Private run `44869789666` checked the source SHA above on 21 November 2026. The job built the Challenge and Solution, inspected the exports, checked the expected types and replayed the Solution. [Job log](https://github.com/flengyel/CategoricalEssentialIncompleteness/actions/runs/44869789666/job/136741506777)

| Check | Verdict | UTC |
| --- | --- | --- |
| Comparator | Passed the comparison of the three theorems and `IsNullaryCalculus` | 05:46:58 |
| Lean 4.35.0-rc2 default kernel | Accepted the Solution export | 05:46:58 |
| NanoDa | Accepted the Solution export | 05:46:26 |
| con-ron | Accepted the Solution export (24,250 declarations) | 05:46:13 |

The raw exports of `Calculus.consistent` differ in the module-qualified names of three instance binders in the type and the corresponding binders in the value. The referenced constants agree. The four designated Challenge placeholders account for all warnings in the Palomar modules. [Export comparison](../scripts/inspect_cei_exports.py)

WSL2 elaborated the current statement audit and both axiom audits from the candidate. The current audit covered all 31,896 declarations in the 1,068 production modules selected by the manifest. The retained audit matched its list of 1,274 declarations. Both reported exactly `propext`, `Quot.sound` and `Classical.choice`. [Current statement audit](../Lean/CategoricalEssentialIncompleteness/CurrentStatementAudit.lean) · [Current axiom audit](../Lean/CategoricalEssentialIncompleteness/CurrentAxiomAudit.lean) · [Retained audit](../Lean/CategoricalEssentialIncompleteness/AxiomAudit.lean)

For the first WSL2 pass, Lean's header parser identified all 2,530 local modules imported transitively by those audit files. Lake's text hashes matched the pre-review sources for every module, and its binary hashes matched all 7,590 compiled objects. The corresponding candidate sources are byte-identical outside comments. WSL2 then ran `lake env env LEAN_PATH="$checked_path" lean` on each candidate audit file, using these verified objects. The two modules with renamed declarations were compiled separately from the candidate and checked by the private workflow.

A separate WSL2 Lake build of the affected dependencies from the candidate is in progress.

The source-policy check and Lean's `--deps-json` parser accepted all 2,568 files. The package uses the repository's pinned toolchain, Lean 4.35.0-rc2. The Challenge has five direct Mathlib imports, and its compiled audit checked all 2,695 transitive imports and the four designated placeholders. The proof-term check found both the exported equivalence and `RestrictionSubobjects.inseparable_iff` in the recovery proof. The Solution and recovery audit checked 56 declarations using the permitted axioms `propext`, `Quot.sound` and `Classical.choice`. The registry entry passed the local Palomar metadata check and its pinned v0.4 schema. All 16 Lake dependencies were clean at their pinned revisions. [Challenge audit](../scripts/check_cei_challenge.lean) · [Source rules](https://github.com/PalomarRegistry/PalomarSubmission/blob/14aa8d6b3c2f14a8540605e37144560b9a00e7e7/scripts/source_requirements.py)

From the repository root, `python3 scripts/verify.py --manuscript-only` checked the 27 records selected by `MANUSCRIPT_CURRENT.json`, including the 24 reachable TeX files, the matching PDFs, the source archive and the v66 correspondence. The candidate preserves the approved title and abstract. [Manifest](../MANUSCRIPT_CURRENT.json) · [Abstract](../manuscript/latex/abstract.tex)

The following commands reproduce the checks from `Lean/`.

```sh
lake build +CEIPalomar.Challenge +CEIPalomar.Solution +CEIPalomar.ManuscriptChecks
lake env lean -DwarningAsError=true ../scripts/check_cei_challenge.lean
lake env lean -DwarningAsError=true CEIPalomar/ManuscriptChecks.lean
lake build +CategoricalEssentialIncompleteness.CurrentStatementAudit +CategoricalEssentialIncompleteness.CurrentAxiomAudit +CategoricalEssentialIncompleteness.AxiomAudit
lake env lean -DwarningAsError=true CategoricalEssentialIncompleteness/CurrentStatementAudit.lean
lake env lean -DwarningAsError=true CategoricalEssentialIncompleteness/CurrentAxiomAudit.lean
lake env lean CategoricalEssentialIncompleteness/AxiomAudit.lean
```

The private workflow adds the pinned toolchain's `nanoda_bin` and `con-ron` to the Comparator configuration under `external_kernels` and invokes `lake comparator --config "$config"`. Run `44856537123` is the earlier result for `e2168b55b1c7e3a291c39ad1e5c613a780406f0a`. [Candidate workflow](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/a65aeb4d5aae48ef9d71bd3352f8935e7612e434/.github/workflows/cei-palomar-check.yml) · [Earlier run](https://github.com/flengyel/CategoricalEssentialIncompleteness/actions/runs/44856537123)
