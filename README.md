# Categorical essential incompleteness

Lean development toward the proof of categorical essential incompleteness in
*Definability and incompleteness in recursion categories*.

The complete formalization of the manuscript remains unfinished. The proved
incompleteness lemmas use restriction domains, predicates, and a representation
section. The numerical recursion and indexing structures are also constructed,
but there is no assembled instance of the full definability-algebra definition
or arithmetic specialization of the Boolean-presentation theorem. A theorem
under weaker hypotheses remains a valid supporting lemma. Completion requires
the compatible structures and model constructions specified in the
[formalization requirements](FORMALIZATION_REQUIREMENTS.md).

## Manuscript

The current note is [Deduction and essential incompleteness in recursion categories](manuscript/deduction_and_essential_incompleteness.pdf)
([LaTeX source](manuscript/deduction_and_essential_incompleteness.tex)). It
constructs theories as closed restriction domains using ranges and Heller's
stable unions, proves the representation-to-inseparability and essential
incompleteness theorems, and verifies the arithmetic instance. The arithmetic
corollary allows a non-c.e. base theory. The new closure construction is not
yet formalized in Lean; the checkpoint described below concerns the existing
development. See the [review and continuation record](Audit/2026-10-29-deduction/README.md).

Version 16 is included with editorial revisions dated 28 October 2026:

- [PDF](manuscript/definability_comparison_v16.pdf)
- [LaTeX source](manuscript/definability_comparison_v16.tex)
- [Source provenance](MANUSCRIPT_SOURCE.json)

The current Lean checkpoint proves incompleteness for represented Boolean
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
