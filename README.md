# Logical consequence and essential incompleteness in recursion categories

**Florian Lengyel** · Manuscript v101 · 26 November 2026

[Read the paper (PDF)](manuscript/logical_consequence_and_essential_incompleteness_v101.pdf) · [Download the LaTeX source (ZIP)](manuscript/logical_consequence_v101_source.zip)

[Manuscript handoff](docs/CODEX_MANUSCRIPT_V101_HANDOFF.md) · [WSL2 verification handoff](docs/CODEX_WSL2_CEI_V101_LEAN_HANDOFF.md)

## Reading the Lean proofs

Appendix E connects seven worked arguments to their Lean declarations. The correspondence table covers the paper’s 77 numbered results and three numbered definitions. [Appendix E](manuscript/latex/appendices/e-reading-lean-proofs.tex) · [Correspondence by theorem](FORMALIZATION_STATUS_V101.md#numbered-statements) · [Lean sources](Lean/CategoricalEssentialIncompleteness/)

[Development of the manuscript](docs/DEVELOPMENT_RECORD.md)

## Abstract

Di Paola and Heller sought an algebraization of generalized incompleteness and proved a diagonal inseparability theorem; we supply one. Instead of beginning with a theory and representing its computable functions, we begin with a recursion category and construct, under additional hypotheses, internal first-order theories in its restriction idempotent completion. Among disjoint pairs $(a,b)$ of restriction idempotents generating consistent theories $T_{a,b}$, exactly the inseparable pairs generate essentially incomplete ones: theories with no complete consistent internal extension in their language. A comparison theorem for range functors gives conditions for diagonal pairs of Turing morphisms to be inseparable; we apply such pairs to internal theories for a categorical form of Smullyan's criterion: a consistent theory strongly separating a recursively inseparable pair has recursively inseparable theorems and refutations. For $(a,b)$ on an object $X$ of propositional atoms, a consistent $T_{a,b}$ with its atom constructor is initial among consistent theories with a sentence assignment on $X$ sending $a$ into theorems and $b$ into refutations. Each such assignment extends uniquely to a translation from it. The construction is left adjoint to the functor giving theorem and refutation subobjects. When $(a,b)$ is inseparable, every consistent theory receiving such a translation is essentially incomplete. Each theory determines a recursion category over its theorem object; under further hypotheses, the theory is essentially incomplete exactly when its copy in the completion is. Examples are Montagna's $S_{\mathrm{PA}}$ (for consistent PA), uniform computations on binary representations of a Miller sequence, and one built from diagrams of c.e. sets presenting cosheaves on a three-point space. In each we prove an internal theory consistent and essentially incomplete.

## Build and verify

The Lean project is in `Lean/`. Elan selects the pinned toolchain. From the repository root, run the manuscript check or the full Lean build, statement checks and transitive axiom audit.

```bash
python3 scripts/verify.py --manuscript-only
bash scripts/verify-wsl.sh
```

For a fresh Linux or WSL2 checkout with Elan installed, `bash scripts/setup-wsl.sh` installs the pinned toolchain, fetches the Mathlib cache and runs the verification. [Manuscript manifest](MANUSCRIPT_CURRENT.json) · [LaTeX build instructions](manuscript/latex/README.md#build)

[Software license](LICENSE) · [Manuscript terms](manuscript/NOTICE.md)
