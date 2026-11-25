# Manuscript v85

The active draft is [manuscript v85](../manuscript/logical_consequence_and_essential_incompleteness_v85.pdf). Its [source archive](../manuscript/logical_consequence_v85_source.zip), [manifest](../MANUSCRIPT_CURRENT.json) and [whole-paper correspondence](../FORMALIZATION_STATUS_V85.md) identify the same edition.

[Lemma 6.4](../manuscript/latex/sections/05a-internal-syntax.tex#L291) now states the finite disjunction for the graph of the chosen primitive-recursive selector. This fixes the entry formula even in a nonstandard model of PA. [Appendix E.5](../manuscript/latex/appendices/e-reading-lean-proofs.tex#L138) gives the source and target of the restriction of the constant-family functor to total morphisms. The proof of Theorem 5.3 uses this functor. [Review that identified the two passages](reviews/V84_FINAL_REFEREE_AND_WRITING/README.md)

The Lean sources are the ones checked at [b37f8908435a4c2991af5b95de4645980ac60a05](https://github.com/flengyel/CategoricalEssentialIncompleteness/tree/b37f8908435a4c2991af5b95de4645980ac60a05). The full receipt at that commit covers v84. For a v85 receipt run the [WSL2 verification assignment](CODEX_WSL2_CEI_V85_LEAN_HANDOFF.md) at the fetched v85 commit. Apply the [project review criteria](../AGENTS.md) to that same revision. [v84 verification](V84_WSL2_LEAN_VERIFICATION.md)

The [repeat review of the published v85 manuscript](reviews/V85_REFEREE_AND_WRITING/README.md) found both corrections in the PDF and no further mathematical or Lean proof defect. The [independent reading](reviews/V85_REFEREE_AND_WRITING/INDEPENDENT.md) covers all ten sections and five appendices. The local wrapper stopped before kernel elaboration because Lean was unavailable.
