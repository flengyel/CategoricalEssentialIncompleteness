# Logical consequence and essential incompleteness in recursion categories

From two disjoint domains in the restriction idempotent completion of a
recursion category we construct a first-order theory that, if consistent,
is essentially incomplete exactly when the domains are inseparable.
The theory is internal to the category of total morphisms in the completion.
Its nonlogical axioms assert the nullary predicates indexed by the first
domain and the negations of the predicates indexed by the second.
On pairs generating consistent theories, the construction is left adjoint
to the functor taking a consistent internal theory to its theorem and
refutation subobjects. We assume that the total category is regular with
disjoint pullback-stable
finite coproducts and that its monomorphisms have partial inverses in the
completion. We require parameter-stable syntax and list algebras and an
initial derivation algebra for each axiom subobject under consideration.

For a consistent theory, partial maps in the slice over its theorem
subobject form a Turing category. With parameterized deduction in the
slices and a chosen global logical theorem, the theory is essentially
incomplete exactly when every consistent closed extension of its
constant family in that slice is incomplete.

In the completed syntactic recursion category for Peano arithmetic (PA), the
numerical interpretation of one total morphism takes each index for a
computably enumerable axiom presentation of a consistent extension of PA
to the code of a sentence independent of that extension.
For a Miller sequence, we expand the theory of real closed
ordered fields by constants naming its terms and axioms giving their
strict rational bounds.
Every consistent extension whose axioms one oracle program semidecides
from every binary representation of the sequence is incomplete.
In a cosheaf construction on a three-point space, each endpoint has a
consistent propositional theory. Every consistent extension in the same
language with a computably enumerable axiom set is incomplete.

The current manuscript and Lean formalization target are **version 70**,
dated 21 November 2026. [Appendix E](manuscript/latex/appendices/e-reading-lean-proofs.tex) explains six Lean proofs. In the contents, numbered sections and appendices appear in blue. [Referee review](docs/reviews/V67_APPENDIX_E/referee.md) · [Mathematical writing review](docs/reviews/V67_APPENDIX_E/writing.md)

The [first-order fork proof](Lean/CategoricalEssentialIncompleteness/V46ForkFirstOrderApplicationChecks.lean)
completes Proposition 10.8. The generated first-order theory restricts to the
original propositional theory and is consistent and essentially incomplete.
At either endpoint, every consistent extension with computably enumerable
axioms in its language is incomplete.

| Item | Location |
| --- | --- |
| Current PDF | [logical_consequence_and_essential_incompleteness_v70.pdf](manuscript/logical_consequence_and_essential_incompleteness_v70.pdf) |
| LaTeX entry point | [manuscript/latex/main.tex](manuscript/latex/main.tex) |
| All LaTeX sources | [manuscript/latex/](manuscript/latex/) |
| Complete source ZIP | [logical_consequence_v70_source.zip](manuscript/logical_consequence_v70_source.zip) |
| Earlier manuscripts and source packages | [manuscript/archive/](manuscript/archive/) |
| Palomar abstract | [docs/PALOMAR_ABSTRACT.txt](docs/PALOMAR_ABSTRACT.txt) |
| Private Palomar package for v66 | [Challenge](Lean/CEIPalomar/Challenge.lean) · [Verification report](docs/V66_LEAN_WRITING_REPORT.md) · [Release and citation instructions](docs/CODEX_WSL2_CURRENT.txt) |
| WSL2 Codex instructions | [docs/CODEX_WSL2_CURRENT.txt](docs/CODEX_WSL2_CURRENT.txt) |

The source directory is `manuscript/latex/`. Its `main.tex` assembles the
sections and appendices. The source ZIP extracts to `latex/`. Earlier PDFs,
standalone TeX files, source ZIPs, and reference manuscripts are kept in
`manuscript/archive/`; their file contents are preserved. The
[archive index](manuscript/archive/INDEX.json) records their former locations
and Git blob hashes.

[Referee review of v64](docs/reviews/V64_2026-11-18/referee.md) · [Writing review of v64](docs/reviews/V64_2026-11-18/writing.md) · [Review of the v62 abstract](docs/reviews/V62_2026-11-17/abstract.md) · [Review of the v61 revisions](docs/reviews/V61_2026-11-17/review.md) · [Review of v60](docs/reviews/V60_2026-11-17/review.md) · [Literature comparisons](docs/reviews/V60_2026-11-17/literature-comparisons.md) · [Manuscript outline](docs/reviews/V60_2026-11-17/outline.md)

## Lean status

The [v65 sentence review](docs/reviews/V65_SENTENCES_2026-11-18/review.md) indexes the paper sentence by sentence and records the wording corrected in v66.

The current correspondence table is
[FORMALIZATION_STATUS_V70.md](FORMALIZATION_STATUS_V70.md). It records 77
numbered results and three definitions. **All 77 numbered results have full Lean counterparts.**
The [guide to the Lean proofs](docs/LEAN_GUIDE_V66.md) links each result and definition to its Lean declarations.
The full v62 replay passed 1,965 commands, including 1,959 strict elaborations
and both complete axiom audits. [Full verification record](docs/V62_FULL_VERIFICATION_2026-11-17.md)
Corollary 10.9 is proved for the two actual fork partial-map slices and every
consistent closed extension. Theorem 5.3 covers both the first-order calculus and the
standalone propositional calculus of Appendix A.6, including nonconstant slice
extensions and the final reduction. See the [independent propositional check](Lean/CategoricalEssentialIncompleteness/V46PropositionalAssociatedIncompletenessChecks.lean). The [full v59 replay](docs/V59_FULL_VERIFICATION_2026-11-14.md)
passed all 1,798 commands at `8df18834734179186459d3c4c34d4c0cf20b6194`, including
1,792 strict elaborations and both complete transitive axiom audits. The
four new finite-support and internal-induction constructions support
Lemma 8.9, completed by the later assembly below. The later [positive-support construction](docs/V59_SIGNED_DERIVATION_FINITE_SUPPORT_2026-11-14.md)
adds the canonical positive-leaf assignment, primitive-recursive extraction,
PA finite atom valuations and their numerical lookup comparison. Its 21-command
incremental verification includes both complete transitive axiom audits.
The [Boolean formula valuation](docs/V59_BOOLEAN_FORMULA_VALUATION_2026-11-14.md) now has its five
constructor laws, five logical schemes, both inference rules and signed-atom
values at arbitrary internal supports. Its 19-command incremental verification
is separate from the earlier full replay. The later
[parameterized substitution proof](docs/V59_PARAMETERIZED_SUBSTITUTION_2026-11-15.md)
proves admissible-substitution invariance, preserves Option failure and
completes all seven logical schemes. Its 25-command incremental verification
includes both complete axiom audits. The later
[internal truth proof](docs/V59_INTERNAL_TRUTH_2026-11-15.md) excludes
contradictory internal signed derivations in every PA model using a common
finite support. Its 23-command incremental verification includes both complete
axiom audits. The later [consistency proof](docs/V59_SIGNED_CONSISTENCY_2026-11-15.md)
proves PA consistency and the generated signed-theory consistency equation
in the predicate category, with generation through regular axiom images.
Its 22-command incremental verification includes both complete axiom audits.
The later [diagonal signed-theory assembly](docs/V59_DIAGONAL_SIGNED_THEORY_2026-11-15.md)
completes Lemma 8.9: the actual diagonal splittings, generated-theory
consistency and all consistent closed extensions are covered. Its
23-command incremental verification includes both complete axiom audits.
The later [arithmetic associated-category proof](docs/V59_ARITHMETIC_ASSOCIATED_CATEGORIES_2026-11-15.md)
completes Corollary 8.10, including arbitrary closed slice extensions, both
split Turing categories and the image of the original arithmetic evaluator.
Its 16-command final incremental verification includes both complete axiom audits.
The later [Miller parameterized-deduction proof](docs/V59_MILLER_PARAMETERIZED_DEDUCTION_2026-11-15.md)
completes Lemma 9.6 for arbitrary nullary coefficients and every printed
signature in every parameter slice. Its 16-command incremental verification
includes both complete axiom audits. The later [Miller associated-category proof](docs/V59_MILLER_ASSOCIATED_CATEGORIES_2026-11-15.md)
completes Corollary 9.8, including arbitrary slice extensions, the Boolean
witness and all comparison functors. Its 22-command incremental verification
includes both complete axiom audits. The later [first-order fork formula proof](docs/V59_FORK_FIRST_ORDER_FORMULA_2026-11-16.md)
constructs formula initiality for arbitrary coefficient diagrams and
atom-identifying transitions. Its 17-command incremental verification
includes both complete axiom audits. The later [parameterized component proof](docs/V59_FORK_PARAMETER_COMPONENTS_2026-11-16.md)
constructs formula folds for arbitrary numerical parameter families and
uniqueness across parameter and atom-label morphisms. Its separate
17-command incremental verification includes both complete axiom audits.
The later [natural parameter fold proof](docs/V59_FORK_NATURAL_PARAMETER_FOLDS_2026-11-16.md) proves the actual
fork constructor square and initiality among componentwise natural relative
formula algebras for arbitrary target families. Its separate 23-command
incremental verification includes both complete axiom audits. The later [canonical diagram syntax proof](docs/V59_CANONICAL_DIAGRAM_SYNTAX_2026-11-16.md) constructs ordinary
initiality for the exact canonical two-sort polynomial and decidable
equality for the specified constant variable diagram. Its separate
16-command incremental verification includes both complete axiom audits.
The later [slice evaluation and target folds](docs/V59_SLICE_EVALUATION_TARGET_FOLDS_2026-11-16.md) compare arbitrary
recursive parameter families and construct natural folds into every
canonical formula target, with component constructor laws and raw
uniqueness. Its separate 17-command incremental verification includes both
complete axiom audits. The later [canonical formula parameter-initiality proof](docs/V59_CANONICAL_FORMULA_PARAMETER_INITIALITY_2026-11-16.md) closes
the source-constructor comparison and proves the full global constructor
law and initiality in every parameter slice, with arbitrary targets and
raw uniqueness. Its separate 17-command incremental verification includes
both complete axiom audits. The later [full fork syntax proof](docs/V59_FULL_FORK_SYNTAX_2026-11-16.md) constructs
the complete term/formula interface and parameter stability, stable lists,
the variable isomorphism, occurrence lists, admissible substitution and
sentence pullbacks. Its separate 20-command incremental verification
includes both complete axiom audits. The later [parameterized deduction proof](docs/V59_FORK_PARAMETERIZED_DEDUCTION_2026-11-17.md) completes
Proposition 10.7: all seven logical schemes and both inference rules have
initial finite derivation algebras in every parameter slice, with natural
folds and raw uniqueness. Arbitrary axiom presentations generate through
regular images. Its separate 18-command incremental verification includes
both complete axiom audits. At that v59 commit the table recorded 75/77, with 10.8 and 10.9 open.
The [full v58 replay](docs/V58_FULL_VERIFICATION_2026-11-14.md)
passed all 1,790 commands at `f0e4b78e83ea21e06b7d335bd8b72353ac25502f`, including every
selected strict producer/check replay and both complete transitive axiom audits.
The earlier full v57 verification of
`45a8a6d017850a3a68fcecd01ad82f5a1a83674a` passed all 1,708 commands,
including the generation, translation, deduction and free first-order
adjunctions (4.4–4.7), Corollary 4.8's incompleteness–inseparability
equivalence, intended-statement checks and both transitive axiom audits.
The [verification record](docs/V57_SIGNED_FIRST_ORDER_VERIFICATION_2026-11-12.json)
identifies that replay's 67-result snapshot and exact tested bytes.
The [Section 5 prerequisite report](docs/V57_SECTION5_PREREQUISITES_2026-11-13.md)
records the new weak-choice, split-product and partial-map functor proofs
and their incremental verification; the numbered-result count is unchanged.
The [split Turing continuation](docs/V57_SPLIT_TURING_2026-11-13.md) proves
the split product laws, universal evaluator, restriction-terminal property
and ambient slice parameter and retraction equations.
The [partial-slice comparison](docs/V57_PARTIAL_SLICE_COMPARISON_2026-11-13.md)
identifies the actual monic partial slice and proves fixed-input restriction
products and universal computations there.
The [arbitrary slice-product continuation](docs/V57_SLICE_PRODUCTS_2026-11-13.md)
adds all binary product laws, the actual slice Turing morphism, terminal
morphisms, total retractions and splitting of slice restriction idempotents.
The [partial-slice completion](docs/V57_PARTIAL_SLICE_COMPLETION_2026-11-14.md)
constructs the literal full recursion subcategory and its splitting equivalence,
preserving restriction in both directions. This completes Lemma 5.1.
The [theory-extension completion](docs/V57_THEORY_EXTENSIONS_2026-11-14.md)
constructs both change-of-base adjunctions, full faithfulness, properness,
composition and the sentence/theorem comparisons in the actual partial
slices. This completes Theorem 5.2.
The [associated-category continuation](docs/V57_ASSOCIATED_RETRACTION_2026-11-14.md)
constructs the evaluation retraction and proves the Boolean totality and
extension equivalences. The [v58 completion](docs/V58_ASSOCIATED_INCOMPLETENESS_2026-11-14.md) proves
closure, consistency and completeness transfer for arbitrary slice extensions,
the full essential-incompleteness equivalence and the final reduction clause.
This completes the first-order statement of Theorem 5.3 with incremental integration and axiom verification.
The [v58 closure-transfer continuation](docs/V58_CLOSED_THEORY_TRANSFER_2026-11-14.md)
constructs mapped rule algebras and closed-theory functors, including ordinary
constant-family and evaluation instances, and verifies the merged v58 target.

The [v58 review](docs/reviews/V58_REVIEW_2026-11-14/summary.md) records
the corrections, reference audit, and source and artifact checks. The [Lean continuation report](docs/V57_LEAN_CONTINUATION_2026-11-10.md)
retains the subsequent proof work and its verification evidence. The current
[WSL2 instructions](docs/CODEX_WSL2_CURRENT.txt) target v70.

The [Google review assessment](docs/reviews/GOOGLE_V58_2026-11-14/assessment.md)
checks its objections against the reviewed v58 text and Lean statements.
Version 59 corrects the publisher line break in reference [18]; all
mathematical text and proof statuses are unchanged.

Lean verification follows the current manuscript. Every manuscript revision
must update `MANUSCRIPT_CURRENT.json`, the correspondence table, source archive,
PDF, and any affected statement checks in the same commit. The verifier checks
the version and bytes of the active sources, checks the archive against those
sources, builds the combined Lean entry point, runs `CurrentStatementAudit.lean`,
and inspects transitive axioms through `CurrentAxiomAudit.lean`. It also checks
imported source and dependency pins and the retained baseline. The permitted
axioms are `propext`, `Quot.sound`, and `Classical.choice`.

The existing `V46` Lean module and namespace names identify implementations.
The active manuscript target is selected by `MANUSCRIPT_CURRENT.json`.

## Clone or use the existing checkout

For a new checkout, use GitHub SSH authentication:

```bash
git clone git@github.com:flengyel/CategoricalEssentialIncompleteness.git
cd CategoricalEssentialIncompleteness
```

For an existing checkout, inspect `git status --short --branch` and
`git remote -v` before updating. Preserve local changes and use the existing
repository. Run the commands below in Debian or another Linux environment,
including WSL2.

## Build and verify Lean

Git, Python 3.9 or later, and Elan are required. The Lake project is in `Lean/`.
Its toolchain and complete dependency manifest are pinned; do not change
Elan's global default or copy another project's compiled files.

| Component | Pin |
| --- | --- |
| Lean | `leanprover/lean4:v4.35.0-rc2` |
| Mathlib | `065356127b1dc0016f66b7283ce0ce2c4055aa55` |
| Foundation | `01f617fbe240a84aaf1c45b31b9d65e0a2e21c1d` |

For an already prepared checkout, run from the repository root:

```bash
bash scripts/verify-wsl.sh
```

For initial setup, `bash scripts/setup-wsl.sh` installs the pinned toolchain,
obtains its Mathlib cache, and invokes verification once. The verification
wrapper takes a project build lock, sets `LEAN_NUM_THREADS=1`, and preserves
the starting commit, Git status, exit status, logs and machine-readable result
in a fresh ignored `.codex-work/verify-*` directory. The underlying verifier
remains `python3 scripts/verify.py` and writes to `build-logs/`.
Run one heavy verification process at a time across projects. WSL2 does not need the hosted
executable-path adapter described in [HOST_BUILD.md](HOST_BUILD.md).

## Build the manuscript

With `latexmk` and the required TeX packages installed, run from the repository
root:

```bash
cd manuscript/latex
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

This produces `manuscript/latex/main.pdf`. The versioned publication PDF remains
in `manuscript/`. The [LaTeX guide](manuscript/latex/README.md) lists the source
files; the source ZIP contains all sections, appendices, and bibliography.

## Provenance and license

[SOURCE_PINS.json](SOURCE_PINS.json) records the imported Lean sources;
[LOCAL_PATCHES.json](LOCAL_PATCHES.json) records their permitted changes.
[MANUSCRIPT_SOURCE.json](MANUSCRIPT_SOURCE.json) records the earlier
manuscript baseline. [MANUSCRIPT_CURRENT.json](MANUSCRIPT_CURRENT.json) records
the current verification target, its source hashes, PDF, and source archive.

The software uses the existing [Apache-2.0 license](LICENSE). Manuscript terms
are specified in [manuscript/NOTICE.md](manuscript/NOTICE.md).
