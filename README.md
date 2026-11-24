# Logical consequence and essential incompleteness in recursion categories

**Florian Lengyel** · Manuscript v84 · 24 November 2026

[Read the paper (PDF)](manuscript/logical_consequence_and_essential_incompleteness_v84.pdf) · [Download the LaTeX source (ZIP)](manuscript/logical_consequence_v84_source.zip)

[Manuscript handoff](docs/CODEX_MANUSCRIPT_V84_HANDOFF.md) · [WSL2 verification handoff](docs/CODEX_WSL2_CEI_V84_LEAN_HANDOFF.md)

## Reading the Lean proofs

Appendix E connects seven worked arguments to their Lean declarations. The correspondence table covers the paper’s 77 numbered results and three numbered definitions. [Appendix E](manuscript/latex/appendices/e-reading-lean-proofs.tex) · [Correspondence by theorem](FORMALIZATION_STATUS_V84.md#numbered-statements) · [Lean sources](Lean/CategoricalEssentialIncompleteness/)

## Abstract

We characterize the disjoint pairs of domains that generate essentially
incomplete first-order theories in the restriction idempotent completion
of a recursion category. The object on which the domains lie indexes
the nullary predicates, the only nonlogical symbols. The axioms are the
atomic sentences indexed by the first domain and the negated atomic
sentences indexed by the second. Under the hypotheses of
[Theorem 4.7](manuscript/latex/sections/03b-internal-adjunctions.tex#L376), a consistent theory so
generated is essentially incomplete if and only if no two complementary
domains contain the given domains, respectively. Here essential incompleteness
means that in every consistent deductively closed extension in the same
language, the join of the theorem and refutation subobjects is a proper subobject
of the sentence object. On pairs generating consistent theories, this
construction is left adjoint to the functor assigning to a consistent
theory its theorem and refutation subobjects.

Under the hypotheses of [Theorem 5.3](manuscript/latex/sections/04-theory-extensions.tex#L261), a
consistent theory is essentially incomplete if and only if its constant
family is essentially incomplete in the slice over its theorem object.
For Peano arithmetic (PA), the numerical interpretation of one total
morphism sends each index for a computably enumerable set of additional
axioms consistent with PA to the code of a sentence independent of the
resulting theory. The other applications concern
real closed ordered fields with constants for the entries of a Miller
sequence and propositional theories obtained from cosheaves on a
three-point space.

## Build and verify

The Lean project is in `Lean/`. Elan selects the pinned toolchain. From the repository root, run the manuscript check or the full Lean build, statement checks and transitive axiom audit.

```bash
python3 scripts/verify.py --manuscript-only
bash scripts/verify-wsl.sh
```

For a fresh Linux or WSL2 checkout with Elan installed, `bash scripts/setup-wsl.sh` installs the pinned toolchain, fetches the Mathlib cache and runs the verification. [Manuscript manifest](MANUSCRIPT_CURRENT.json) · [LaTeX build instructions](manuscript/latex/README.md#build)

[Software license](LICENSE) · [Manuscript terms](manuscript/NOTICE.md)
