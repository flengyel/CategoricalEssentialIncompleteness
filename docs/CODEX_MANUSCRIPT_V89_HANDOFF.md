# Manuscript v89

[Paper](../manuscript/logical_consequence_and_essential_incompleteness_v89.pdf) · [LaTeX source](../manuscript/logical_consequence_v89_source.zip) · [Correspondence](../FORMALIZATION_STATUS_V89.md)

In Lemma A.7 the image inclusion $m$ and its partial inverse $r$ give a restriction idempotent $mr$ fixing $f$. The definition of range gives $\operatorname{ran}(f)\le mr$. Conversely, factoring $m$ through the splitting of any restriction idempotent $a$ fixing $f$ gives $mr\le a$. The lemma applies this to $a=\operatorname{ran}(f)$. Its hypotheses and conclusion agree with v88.

The Appendix A review covers categorical hypotheses, syntax, substitution, inference algebras and the first-order and propositional theories. The endpoint formula in Appendix B.4 was checked for v88. [Endpoint check](reviews/V88_REFEREE_AND_WRITING/ENDPOINT.md)

The Lean tree, verifier and dependency pins match v88. The last full kernel receipt is for v84. [WSL2 handoff](CODEX_WSL2_CEI_V89_LEAN_HANDOFF.md) · [v84 verification](V84_WSL2_LEAN_VERIFICATION.md)
