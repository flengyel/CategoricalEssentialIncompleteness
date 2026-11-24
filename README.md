# Logical consequence and essential incompleteness in recursion categories

**Florian Lengyel** · Manuscript v82 · 24 November 2026

[Read the paper (PDF)](manuscript/logical_consequence_and_essential_incompleteness_v82.pdf) · [Download the LaTeX source (ZIP)](manuscript/logical_consequence_v82_source.zip)

## Reading the Lean proofs

Appendix E connects seven worked arguments to their Lean declarations. The correspondence table covers the paper’s 77 numbered results and three numbered definitions. [Appendix E](manuscript/latex/appendices/e-reading-lean-proofs.tex) · [Correspondence by theorem](FORMALIZATION_STATUS_V82.md#numbered-statements) · [Lean sources](Lean/CategoricalEssentialIncompleteness/)

## The construction

We realize Di Paola and Heller's objective to give an algebraic account
of generalized incompleteness theorems in recursion categories.
Let $a,b$ be disjoint domains on an object $X$ in the restriction
idempotent completion of a recursion category. In its total category the
domains have inclusions $i_a:A\hookrightarrow X$ and $i_b:B\hookrightarrow X$.

Take $X$ as the object of predicate symbols. These are the only nonlogical
symbols, and they take no arguments. Let $S_X$ be the object of sentences.
The atomic sentence constructor is a morphism $\theta_X:X\to S_X$.
For any object $W$, a morphism $x:W\to X$ specifies a predicate symbol
over $W$. Its atomic sentence over $W$ is $\theta_X\circ x:W\to S_X$.

Restricting the constructor to $a$ gives the positive axiom family
$\theta_X\circ i_a:A\to S_X$. For the negative axioms, restrict it to
$b$ and apply sentence negation $\nu_X:S_X\to S_X$. This gives
$\nu_X\circ\theta_X\circ i_b:B\to S_X$.
The join of the two image subobjects gives the nonlogical axioms.
Closing them under the rules of deduction gives the theory $T$.

A consistent $T$ is essentially
incomplete if every consistent deductively closed extension in the same
language is incomplete. We prove that, for consistent $T$, this holds
if and only if no complementary domains $c,d$ on $X$ satisfy
$a\leq c$ and $b\leq d$.

For pairs generating consistent theories, this construction is left adjoint
to the functor taking a consistent theory to its theorem and refutation
subobjects. We assume that the total category is regular with disjoint,
pullback-stable finite coproducts and that its monomorphisms have partial
inverses in the completion. The variable object has decidable equality,
the syntax and variable-list algebras are initial in each parameter slice,
and each presentation has an initial derivation algebra for every axiom subobject.

For a sentence theory $u:U\hookrightarrow S$, partial maps in the slice
over $U$ form a Turing category. Assume that every axiom subobject in
each slice has an initial derivation algebra and that a logical theorem
$\lambda:1\to S$ factors through each consistent theory.
Then passage from $u$ to its constant family
$1_U\times u:U\times U\hookrightarrow U\times S$ preserves and reflects
essential incompleteness of consistent theories.

In the completed syntactic recursion category for Peano arithmetic (PA),
the numerical interpretation of one total morphism sends each index for a
computably enumerable axiom presentation of a consistent extension of PA
to the code of an independent sentence for that extension.
For a Miller sequence, we add to the theory of real closed ordered fields
constants for its terms and axioms giving their strict rational bounds.
Every consistent extension in this language is incomplete if it
admits an axiom set semidecided by one oracle program from every binary
representation of the sequence. In a cosheaf construction on a three-point
space, the propositional theory at each endpoint is consistent, and every
consistent extension in its language with a computably enumerable axiom
set is incomplete.

## Build and verify

The Lean project is in `Lean/`. Elan selects the pinned toolchain. From the repository root, run the manuscript check or the full Lean build, statement checks and transitive axiom audit.

```bash
python3 scripts/verify.py --manuscript-only
bash scripts/verify-wsl.sh
```

For a fresh Linux or WSL2 checkout with Elan installed, `bash scripts/setup-wsl.sh` installs the pinned toolchain, fetches the Mathlib cache and runs the verification. [Manuscript manifest](MANUSCRIPT_CURRENT.json) · [LaTeX build instructions](manuscript/latex/README.md#build)

[Software license](LICENSE) · [Manuscript terms](manuscript/NOTICE.md)
