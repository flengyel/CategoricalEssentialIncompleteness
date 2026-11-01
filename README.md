# Logical consequence and essential incompleteness in recursion categories

The current manuscript is [Logical consequence and essential incompleteness in recursion categories, version 27](manuscript/logical_consequence_and_essential_incompleteness_v27.pdf)
([LaTeX source](manuscript/local_connectedness/main.tex),
[source archive](manuscript/logical_consequence_v27_source.zip), 1 November 2026).

Section 3 proves the comparison theorem for lifted partial conditionals;
Section 4 applies it to interpreted sentence theories. Section 5 realizes
categorical syntax in the total restriction splitting of the syntactic category.
Section 6 constructs soundness factorizations for the standard code interpretation
and its ultrapowers, using a separate model of the represented axioms.
Section 7 applies the comparison through partial proof search. Section 7.2
constructs an indexed family of arithmetic theories and identifies its numeral
fibers categorically. Section 7.3 constructs one total morphism assigning an
independent sentence to every consistent standard presentation. Section 7.4
proves the numerical realization, including its parameterized universal properties
and proof-code comparisons. Section 7.5 applies numerical incompleteness; Section 7.6
treats numeral instances and extensions. Sections 8 and 9 contain the Miller-sequence
and three-point-cosheaf applications.

Appendix A constructs categorical syntax, substitution, and deductively closed
theories. Appendix B constructs the cosheaf category; Appendix C gives the
lifting counterexample. Appendix D contains the faithful model family, ambient
theory extension, and numeral observations. The introduction and abstract remain
reserved for the final revision. The [source directory guide](manuscript/local_connectedness/README.md)
lists the files and build command.

The [theorem-and-proof plan](Plans/comparison_soundness_paper_plan_v2.pdf)
and [version 20 reviews](Audit/2026-11-01-comparison-v20/README.md)
record the organization and preceding review. The current manuscript has not
been reconciled with the Lean declarations.

The [version 27 review record](Audit/2026-11-01-numerical-consolidation-v27/README.md)
records one consolidation of the numerical foundations. Section 7.4 now contains
the shared category, regularity proof, and restriction equivalence in both
directions; Appendix B cites it while retaining its componentwise arguments.
All applications remain. The preceding
[version 26 review record](Audit/2026-11-01-numerical-v26/README.md)
records the numerical first-order realization and its proof-code comparison.

The active Lean target is the [version 5 local-connectedness paper](manuscript/essential_incompleteness_via_local_connectedness_v5.pdf),
as specified in [the continuation instructions](CONTINUATION_LEAN_LOCAL_CONNECTEDNESS.md).
The abstract categorical chain through Corollary 6.7, its combined theorem,
and the syntactic application through the exact faithful model family and
specified finite two-test switch are proved. The arithmetic application now
derives recursive inseparability and incompleteness through that categorical
chain, with explicit sentence/proof objects and both substitution inclusions.
All 24 numbered results, including the three-point construction, applications
and Appendices A–C, are proved. The required unnumbered constructions are also
implemented, including word-semigroup universality, endpoint probes and standard
observations. The status record distinguishes this scope from one cited
background theorem that has not been independently formalized.
[FORMALIZATION_STATUS.md](FORMALIZATION_STATUS.md) tracks all 24 numbered results,
their Lean declarations, and the remaining obligations. Run
`python3 scripts/verify.py` to build the project and audit its proof dependencies.

## Earlier development

Research notes and a Lean development on categorical essential incompleteness.
The earlier account connects a Turing morphism, computational inseparability,
polynomial finite-proof algebras, and theorem ranges. It proves essential
incompleteness for a numerical classical deductive presentation and gives a
general construction under explicit structural hypotheses. A further note
derives the finite-stage domain unions from Heller's iteration structure,
proves consistency without decidable atom equality, and constructs a
nonnumerical computational cosheaf example.

## Earlier manuscripts

The note [Domains, finite proofs, and essential incompleteness](manuscript/domains_hoare_profunctors_essential_incompleteness.pdf)
([LaTeX source](manuscript/domains_hoare_profunctors_essential_incompleteness.tex),
29 October 2026, 23 pages). It includes Hoare profunctors and their relation
to polynomial bicomodules, the numerical obstruction to weakest liberal
preconditions, the explicit Turing-morphism inseparability proof, computational
finite-proof initial algebras, and the proof-range construction. Section 13
states the general logical-presentation existence problem. No appendix remains.

The [outline, mathematical review, writing review, and verification record](Audit/2026-10-29-polynomial-proofs/README.md)
accompany the note. This account has not been formalized in Lean. The existing
Lean checkpoint described below concerns the earlier development.

The supplement [Finite proof algebras in range restriction categories](manuscript/general_recursion_category_construction.pdf)
([LaTeX source](manuscript/general_recursion_category_construction.tex))
constructs typed constructor maps and uses a Turing morphism to produce partial
folds. Specified stable domain unions then give initial proof algebras. A finite
valuation argument proves consistency under explicit regularity and equality
hypotheses, and inseparability gives essential incompleteness. The supplement
credits Heller's range counterexample and examines a selected presheaf completion.
Its [review record](Audit/2026-10-29-general-construction/README.md) and
[continuation prompt](CONTINUATION_GENERAL_RECURSION_CATEGORIES.md) identify the
construction problems at that stage. These results have not been formalized in Lean.

The continuation [Iteration domains, finite proofs, and computational cosheaves](manuscript/iteration_domains_and_cosheaves.pdf)
([LaTeX source](manuscript/iteration_domains_and_cosheaves.tex), 14 pages)
constructs the stage union as a finite-worklist termination domain. It proves
regularity and range/image agreement from weak choice and the stated range
and finite-limit hypotheses, gives an equality-free finite-proof consistency
argument, and verifies the construction in computational cosheaves on the
Sierpiński space. Its universal object has no decidable equality. Heller's
definitions and Lengyel's 2004 paper are read together with the version-10
[errata](https://github.com/flengyel/errata/tree/5555e4fa1da7b8e3a0836dd1fbf1ca385cacd03b/lengyel2004).
The [source checks, author-side reviews, and verification](Audit/2026-10-29-iteration-cosheaves/README.md)
record the scope of the results. No new result has been formalized in Lean.

The companion [Range completion and computational cosheaves on a three-point space](manuscript/range_completion_three_point_cosheaves.pdf)
([LaTeX source](manuscript/range_completion_three_point_cosheaves.tex))
identifies the established free range completions and proves an obstruction
to preservation of the original Turing morphism. It constructs the
three-point cosheaf example with a nontrivial cover, effective global pushout
presentations, internal regular images, explicit frames, and a compatible
Turing morphism. The finite-proof construction applies without decidable atom
equality. The [reviews and verification](Audit/2026-10-29-range-three-point/README.md)
separate proved facts from the remaining recursion-preserving completion
problem in the [continuation prompt](CONTINUATION_GENERAL_RECURSION_CATEGORIES.md).

The note [Inseparable domains and computational extensions](manuscript/inseparable_domains_and_extensions.pdf)
([source](manuscript/inseparable_domains_and_extensions.tex), 5 pages)
constructs the signed-literal presentation `(U+U, swap, a+b)` directly from
an inseparable pair. It proves an adjunction and an exact equivalence:
inseparability means that every consistent selected extension of this
presentation is incomplete. This construction needs binary restriction
coproducts and finite domain joins, with no range or proof-algebra assumption.
For the existing classical theories, the fixed atom map proves the stronger
inseparability of every extension's theorem/refutation pair. Restriction
functors preserving zero and domain joins reflect inseparability; a projection
of Heller recursion categories shows that even Turing-morphism-preserving functors
need not preserve a specified pair. The signed presentation does not construct
a full classical deductive closure. The [reviews and verification](Audit/2026-10-29-inseparable-extensions/README.md)
record this distinction and the remaining construction problem.

The [review of the existing syntactic categories S_T](Audit/2026-10-29-separator-transfer/README.md)
starts from their valid uniform provability quotient. The actual extension
functors preserve identity, zero, and the chosen Turing morphism. The sets
of program indices proved equal to identity and zero form a recursively
inseparable pair, and extension enlarges both sets. Completeness would
decide identity membership by proof search. This gives a short PA benchmark
and records effective proof observations. It supplies a comparison on presentations and domain
observations, not a functor on all morphisms from S_T to the recursion category
of partial recursive functions.
The [other-theory applications](Audit/2026-10-29-separator-transfer/OTHER_THEORIES.md)
reuse S_T through effective interpretations, including ACA_0, finite set
theory and HA via negative translation. They connect the argument with
Bernardi's established theory of precomplete equivalence relations and
give a related inseparable-class proof for c.e. lambda theories.

The paper [Local connectedness, range functors, and essential incompleteness](manuscript/essential_incompleteness_via_local_connectedness_v5.pdf)
([source](manuscript/essential_incompleteness_via_local_connectedness_v5.tex), Version 5, 30 October 2026, 28 pages)
uses a locally connected target to establish recursive inseparability in a
source recursion category that need not be locally connected, and applies
the result to essential incompleteness.
Theorem 6.3 gives inseparable restriction idempotents; Corollary 6.7 transfers
this inseparability to the restriction idempotents representing theorems and
refutable formulas of every consistent extension. Corollary 7.1 applies this
to PA using the recursion category of partial recursive functions, c.e. proof carriers,
conclusion ranges, and numeral substitution. No soundness of the extensions
is assumed.

The [sentence-by-sentence terminology and definition-order review](Audit/2026-10-30-sentence-review-v5/README.md)
records the full reading coverage, corrections, and build checks for this version.

The faithful model-family functor `F_T:S_T→∏_M Pfn` is a separate
application of the lifting theorem. Its target is locally connected;
`S_T` itself is not locally connected for consistent c.e. extensions of PA.
One program supplies each required lift for complementary source restriction
idempotents.
The general theorem does not require preservation of products, although
these particular model functors preserve them.

The three-point construction gives a recursion category not restriction-
equivalent to the recursion category of partial recursive functions.
Its positive and negative atomic axioms
use exactly the inseparable pair supplied by Theorem 6.3. Corollary 6.7
proves internal essential incompleteness, and Theorem 8.2 additionally
proves recursive inseparability of the endpoint observations.
Appendices A–B contain the structural, Turing, syntax, proof and consistency
arguments. Appendix C treats only the theorem with its lifting hypothesis
removed. The lifting criterion and proof remain in Section 6.2.

The introduction includes the Di Paola–Heller program and the relevant
literature, cites Lengyel 2004 together with the version-10 corrections,
and explains the exclusion of the primed systems by
[the composition-failure result](https://arxiv.org/abs/2609.25556).
No private-note citation substitutes for an argument in this paper.
The [Version 5 wording review](Audit/2026-10-30-literature-and-terminology/FRONT_MATTER_V5.md)
and [Version 4 front-matter review](Audit/2026-10-30-literature-and-terminology/FRONT_MATTER_V4.md)
record the revised abstract and shorter introduction, including the gluing
of two Sierpiński spaces underlying the three-point example.
The [Version 3 terminology and literature record](Audit/2026-10-30-literature-and-terminology/README.md)
and [literature comparison](Audit/2026-10-30-literature-and-terminology/LITERATURE_COMPARISON.md)
record the terminology and abstract corrections, removal of irrelevant
disclaimers, and comparison with earlier work.
The [Version 2 outline and reviews](Audit/2026-10-29-introduction-economy/README.md)
remain the historical mathematical and writing checks for that version.
These are paper proofs, not new Lean formalizations.

The separate comparison [Internal theories and intrinsic incompleteness](manuscript/intrinsic_introspection_and_extensions.pdf)
([source](manuscript/intrinsic_introspection_and_extensions.tex)) applies Ramesh's
results in the initial arithmetic universe. It constructs no comparison from
the given recursion category and identifies none of its selected computational
domains or theory extensions. It therefore discharges none of the remaining
Di Paola–Heller construction obligations. See the
[scope correction](Audit/2026-10-29-intrinsic-introspection/SCOPE_CORRECTION.md).

Earlier notes remain available in [the manuscript directory](manuscript/README.md).

Version 16 is included with editorial revisions dated 28 October 2026:

- [PDF](manuscript/definability_comparison_v16.pdf)
- [LaTeX source](manuscript/definability_comparison_v16.tex)
- [Source provenance](MANUSCRIPT_SOURCE.json)

## Earlier Lean checkpoint

The earlier Lean checkpoint proves incompleteness for represented Boolean
quotients along `J : Tot(K₀) → C`, under the stated representation hypotheses.
Its statement includes a regular extensive category `C`, a functor `J`, a natural identification
of global predicates with subobjects along `J`, the internal representation
section, and nontriviality `1_U ≠ 0`. Every consistent Boolean quotient whose
two bound fibers arise from restriction idempotents is incomplete.

The proof constructs the domain equalizers, totality pullbacks, internal
total-arrow operations, and restriction inverse image. It proves the internal
factorization `Sep → Z_U`, identifies global total arrows with `Tot(K₀)`, and
identifies global domains with ordinary restriction idempotents. The predicate
identification gives a natural isomorphism of presheaves and a natural
injective bounded lattice map from domains to subobjects. The internal
section also supplies the external diagonal representation equations.

The Boolean-presentation lemma is proved: consistency is equivalent to the
bound copairing being monic, completeness to its being a regular epimorphism,
and both together to its being an isomorphism. The quotient argument also
proves that the bound copairing is not a regular epimorphism.

Characteristic arrows for complementary subobjects and the internal Boolean
algebra on `1 + 1` are constructed. The equivalence between complete represented
Boolean extensions and represented decisions is proved, including the
comparison through the domain-to-predicate embedding and the functor `J`.
`EnrichedRestriction.represented_boolean_quotient_incomplete` is the supporting
lemma using restriction, lattice, predicate, and section data. Its name does
not identify it with the manuscript's full definability-algebra interface.
The numerical model's additional recursion and indexing structures are proved
separately; a compatible assembled instance is not yet provided.

The numerical restriction category and the category of arbitrary PERs on
`ℕ` are constructed. The functor from total numerical arrows to equality
PERs is full and faithful and preserves binary products. The PER category is regular: it has
finite limits and coequalizers of kernel pairs, and its regular epimorphisms
are stable under pullback. It is also finitely extensive: coproducts are
disjoint and satisfy the van Kampen property. Restriction domains correspond to c.e. supports,
and complementary domains on `ℕ` correspond exactly to recursive sets.
Support inclusions are subobjects with the stated order and pullback
properties; dovetailing proves that c.e. unions are their categorical joins.
Restriction domains and full PER subobject lattices define predicate functors
on total numerical arrows. The domain inclusion is an injective natural
bounded lattice homomorphism, preserving and reflecting complementarity of
a specified pair. Arrows from the equality PER on `ℕ` to the Boolean PER
correspond bijectively to total recursive Boolean functions. Their upper
fibers are exactly the recursive support inclusions, which are exactly the
complemented subobjects of that equality PER.
Partial pairing and recursive tuple coding give the numerical category a
prodominical `P`-category structure with its original restriction operation.
The induced total-arrow category is equivalent to the existing one, with
compatible product pairings. The domain lattices are naturally isomorphic
under restriction inverse image; their joins are constructed from c.e. unions.
Computable increasing enumeration and counting give recursive isomorphisms
between every numerical object and `ℕ`. The universal partial recursive
evaluator satisfies the Turing factorization property for every numerical
parameter object, giving a recursion-category instance. Choosing a program
code for each partial arrow defines a set-level indexing function with the
required evaluation equation.
The numerical hom-sets and their operations define enriched restriction
hom-objects in `Type`. The domain equalizers and totality pullbacks are
identified with numerical domains and total arrows. Their lattice and product
operations agree for families at every parameter type. The indexing function
lifts to an internal morphism whose composite with evaluation is the identity.
Full PER subobjects give internal predicates with a monic natural domain
embedding. Evaluation of global arrows gives equivalences with the numerical
partial and total categories, preserving restriction, partial pairing, and
binary products of total arrows.
The global predicate functor is naturally identified with the full PER
subobject functor, and its induced domain embedding agrees with support
inclusion.
For disjoint supports, absence of a complementary-domain separator is
equivalent to recursive inseparability.

Canonical arithmetic sentence codes form an infinite recursive set with a
computable enumeration and inverse. Numeral substitution is computable jointly
in the unary-formula code and numeral and defines a total numerical arrow.
Its representation equations are equivalent to strong numeralwise definability.
The internal representation projection has a section exactly when every
recursive set is strongly definable numeralwise in the theory.
The internal categorical diagonal theorem then proves recursive inseparability
of theorem and refutation indices. For c.e. theories, both supports are c.e.
and are represented by numerical restriction domains.

Every consistent c.e. extension of a consistent arithmetic theory strongly
defining every recursive set is incomplete. Every consistent extension has a
nonrecursive theorem support. These results apply in particular to consistent
extensions of `PA⁻`. The general theorem assumes neither that the original
theory is c.e. nor that it extends `PA⁻`.

The Lindenbaum Boolean presentation, its theory-extension correspondence,
and the arbitrary-effective-language generalization remain open; see
[the declaration-to-manuscript correspondence](FORMALIZATION_STATUS.md).
The imported categorical and arithmetic foundations remain available.
The entry point is
[`CategoricalEssentialIncompleteness.lean`](Lean/CategoricalEssentialIncompleteness.lean).

## Clone and build on Debian, Linux, or WSL 2

The same build commands run on native Linux and on Linux under WSL 2. On
Windows, run them in the Debian or Ubuntu WSL 2 terminal. WSL is optional;
native Debian uses its normal terminal.

### Install prerequisites

Git, Python 3.9 or later, and the Lean toolchain manager `elan` are required.
On Debian or Ubuntu, including those distributions under WSL 2:

```bash
sudo apt update
sudo apt install -y git curl python3 build-essential ca-certificates
```

If `elan` is not already installed, follow the
[official Lean installation instructions](https://lean-lang.org/install/manual/):

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
source "$HOME/.elan/env"
```

### Clone and set origin

Use SSH when your GitHub SSH key is already configured. You can check the
recognized account with `ssh -T git@github.com`; after successful authentication,
GitHub's message that it does not provide shell access is expected.

```bash
git clone git@github.com:flengyel/CategoricalEssentialIncompleteness.git
cd CategoricalEssentialIncompleteness
git remote set-url origin git@github.com:flengyel/CategoricalEssentialIncompleteness.git
git remote -v
git branch -vv
```

`git clone` creates `origin` and makes the local `main` branch track
`origin/main`. The `set-url` command explicitly sets the intended repository
URL. `git remote -v` should show the SSH URL for both fetch and push.

HTTPS remains an alternative:
`https://github.com/flengyel/CategoricalEssentialIncompleteness.git`.
HTTPS uses separate authentication and does not use your SSH key. If credentials
are required, use a GitHub credential manager or a personal access token;
GitHub account passwords are not accepted for Git operations over HTTPS. See
[GitHub's authentication guidance](https://docs.github.com/en/get-started/git-basics/about-remote-repositories).

For an existing Git checkout, run the following from its root to add `origin`
if it is missing, or correct its URL if it already exists:

```bash
if git remote get-url origin >/dev/null 2>&1; then
  git remote set-url origin git@github.com:flengyel/CategoricalEssentialIncompleteness.git
else
  git remote add origin git@github.com:flengyel/CategoricalEssentialIncompleteness.git
fi
git fetch origin
git branch --set-upstream-to=origin/main main
git remote -v
```

This configures the remote and upstream for an existing local `main` branch;
it does not merge or replace local work. Prefer cloning for a fresh checkout
with the repository's commit history.

### Run compilation and verification

From the repository root, download the cached Mathlib build and run the
verification script:

```bash
cd Lean
lake exe cache get
cd ..
python3 scripts/verify.py
```

The toolchain file selects Lean `4.35.0-rc2` automatically through `elan`; the
manifest pins every dependency. The script uses one Lean thread by default,
checks the imported source and manuscript hashes and dependency revisions, builds
`CategoricalEssentialIncompleteness`, and checks the transitive axiom dependencies
of all nine Failure of Composition solution declarations and 449 diagonal,
restriction, internal, global-comparison, categorical, Boolean-presentation,
decision, numerical, and arithmetic declarations (458 in total). Only
`propext`, `Classical.choice`, and `Quot.sound` are accepted.

A successful run ends with:

```text
PASS: project build, dependency pins, source hashes, and 458 axiom audits.
```

For compilation alone, run from the repository root:

```bash
cd Lean
lake build CategoricalEssentialIncompleteness
cd ..
```

Fresh logs and the machine-readable result are written to `build-logs/`, which
is ignored by Git. The arithmetic syntax, representation, and incompleteness evidence is in
[`Audit/2026-10-28-arithmetic-syntax/`](Audit/2026-10-28-arithmetic-syntax/).
The numerical enrichment and global-comparison evidence is in
[`Audit/2026-10-29-numerical-enrichment/`](Audit/2026-10-29-numerical-enrichment/).
The numerical recursion-category and indexing evidence is in
[`Audit/2026-10-29-numerical-recursion/`](Audit/2026-10-29-numerical-recursion/).
The numerical restriction-product and comparison evidence is in
[`Audit/2026-10-29-numerical-restriction-products/`](Audit/2026-10-29-numerical-restriction-products/).
The Boolean-arrow and complemented-subobject evidence is in
[`Audit/2026-10-29-numerical-boolean/`](Audit/2026-10-29-numerical-boolean/).
The numerical predicate and domain-embedding evidence is in
[`Audit/2026-10-29-numerical-predicates/`](Audit/2026-10-29-numerical-predicates/).
The PER coproduct and extensivity evidence is in
[`Audit/2026-10-28-per-extensive/`](Audit/2026-10-28-per-extensive/).
The PER regularity evidence is in
[`Audit/2026-10-28-per-regular/`](Audit/2026-10-28-per-regular/).
The product, finite-limit, and regular-image evidence and
the editorial review are in
[`Audit/2026-10-28-per-limits/`](Audit/2026-10-28-per-limits/).
The numerical-category and support-comparison evidence is in
[`Audit/2026-10-28-numerical-supports/`](Audit/2026-10-28-numerical-supports/).
The global-comparison and categorical-theorem evidence is in
[`Audit/2026-10-28-global-comparison/`](Audit/2026-10-28-global-comparison/).
The enriched-restriction checkpoint evidence is in
[`Audit/2026-10-28-enriched-restriction/`](Audit/2026-10-28-enriched-restriction/).
The internal-separator checkpoint evidence is in
[`Audit/2026-10-28-internal-separator/`](Audit/2026-10-28-internal-separator/).
The decision checkpoint evidence is in
[`Audit/2026-10-28-decisions/`](Audit/2026-10-28-decisions/).
The Boolean-presentation checkpoint evidence is in
[`Audit/2026-10-28-boolean-presentations/`](Audit/2026-10-28-boolean-presentations/).
The diagonal checkpoint evidence is in
[`Audit/2026-10-28-diagonal/`](Audit/2026-10-28-diagonal/); the initial foundations
evidence is retained in [`Audit/2026-10-28/`](Audit/2026-10-28/).
See [`BUILD_RESULT.md`](BUILD_RESULT.md).
The hosted environment's executable-path adapter,
[`scripts/host_proc_self_compat.c`](scripts/host_proc_self_compat.c), is documented
in [`HOST_BUILD.md`](HOST_BUILD.md). Ordinary Linux and WSL 2 builds do not need it.

## Imported foundations

The entry point imports `PCats`, `RiceShapiro`, `Metamath`, `Arith`,
`CategoricalRiceShapiro`, `FailureOfComposition`, and the nine proved solution
declarations. It checks that the concrete typed arithmetic category instantiates
the existing `PRecursionCategory` interface and that its evaluator
satisfies the Turing factorization property. Imported libraries retain their
existing module names.

| Component | Revision |
| --- | --- |
| Categorical_Rice_Shapiro | `cb0622c864f50372f5ddc1882a6c66c31144c70e` |
| FailureOfComposition | `506d1f1494d6c05b0ba304edf5fe0bfa6c32864b` |
| Mathlib | `065356127b1dc0016f66b7283ce0ce2c4055aa55` |
| Foundation | `01f617fbe240a84aaf1c45b31b9d65e0a2e21c1d` |

[`SOURCE_PINS.json`](SOURCE_PINS.json) records the original Git blob hash of each
imported file. [`LOCAL_PATCHES.json`](LOCAL_PATCHES.json) records the proof
compatibility repair, root-package rename, thirteen comment-only imported-source
revisions, and manuscript revisions with exact before/after hashes.
The root Lake configuration adds this project's entry point.

The Rice–Shapiro tree supplies the shared sources. Two shared Lean files differ
between the original repositories: its `FailureOfComposition.lean` imports the
additional developments, and its `ConcreteEvaluatorGraph.lean` expresses
`eventualGraph` using explicit substitution and adds `eventualGraph_val`.
Both files are retained from Rice–Shapiro. One proof in
`Palomar/EvaluatorBridge.lean` is adapted to rewrite with the proved
`eventualGraph_val` characterization. Its theorem statement is unchanged. The
exact diff and original build failure are retained in the audit directory.

This checkpoint does not assert completion of categorical Rice–Shapiro or
identification of every concrete category with the manuscript's intended
category. Open hypotheses in the imported development remain explicit.

## Palomar toolchain and checker

On 2026-10-28, PalomarSubmission revision
`a93fc88c092faeef1a92b1c905e688aab8e80795` specifies a minimum source toolchain
of Lean `v4.35.0-rc2`. Its independent con-ron checker for that source toolchain
is taken from Lean `v4.36.0-rc1`, release commit
`c9afcddf514a6772bd4d649f7cfc04eff0b9f15e`. Lean, Lake, the exporter, and NanoDa
remain tied to the submitted source toolchain. The inspected policy files and
their source links are retained in the audit directory.

The recorded validation consists of Lean compilation and transitive axiom
inspection. This repository has not undergone Palomar Comparator or
independent-kernel verification and does not inherit the original project's
registry verification.

## License

The Lean and supporting software are distributed under the existing
[Apache License 2.0](LICENSE). The manuscript retains its existing copyright
and licensing terms; no additional manuscript license is granted here. See
[the manuscript notice](manuscript/NOTICE.md).













