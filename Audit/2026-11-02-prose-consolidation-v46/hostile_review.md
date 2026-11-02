# Version 46 author-side hostile audit

This is an author-side audit of the version-46 revision, not an independent peer review. Target: `tmp/revision46/frozen`; comparison: `tmp/revision46/baseline` and `full.diff`. The issue axes checked were correctness and preservation of mathematical content during prose, inline-formula, and consolidation edits. No manuscript source was edited.

## (A) Kill-shots / hard blockers

None established in the reviewed changes.

## (B) Major weaknesses

No concrete required correction established in the reviewed changes.

## (C) Minor issues

No concrete required correction established. The audit does not require restoring deleted recaps or re-creating cited proofs locally.

## (D) Cross-section consistency failures

None established. In particular:

- **Lemma 6.2:** `sections/06-interpretation-in-models.tex:74–96` retains the tagged relation's $T$-provable functionality and totality, applies precisely the functional-graph clause of Lemma 5.2, and retains the verification in each model and the unique-section argument. Search-program construction is consolidated without replacing the model argument.
- **Appendix D.2:** `appendices/d-faithful-family.tex:75–115` retains the theory-extension functor $Q$, preservation of its specified structure, the target Turing factorization, and the application to $T'$. The references to Corollary 6.3 supply the repeated model-pair argument.
- **Miller conditionals:** `sections/04-miller-sequences.tex:150–163` uses the compatible joins established in Proposition 8.2 and the conditional result of Proposition 3.4. The totality assertion and both branch equations remain. The cited result supplies the representation-independent partiality argument.
- **Three-point consolidation:** `sections/09-three-point-space.tex:174–180` cites the exact categorical non-equivalence statement proved in Appendix B. The endpoint calculation at lines 220–229 cites `eq:fork-turing-endpoint` and retains the total parameter map $z\mapsto(0,s(z))$. Removing the local-connectedness lead-in removes no hypothesis used by the conditional argument.
- **Distinct proof obligations:** the syntactic initiality proof still proves existence and uniqueness in $T$ for arbitrary internal algebras and parameters. The numerical realization still proves halting and uniqueness for the corresponding recursive morphisms. The two are not collapsed. The partial proof-search lift in `sections/08-essential-incompleteness-of-arithmetic.tex:135–179` still relies only on the search lemma's one-sided graph and domain equivalence; its model-functional argument remains separate from the total source-conditional construction.
- **Appendix scope and naturality:** the edited Appendix A retains its stated categorical hypotheses, equation types, algebra uniqueness, and range/splitting data. Appendix B retains cosheaf naturality. Appendix C retains the distinction between ordinary recursive specialization of codes and execution relative to an oracle, including the equalities of domains and values.

## (E) Acceptance conditions, non-negotiable

No correction is required by this audit before accepting the version-46 revision within its stated scope. This is not a publication-acceptance judgment on the complete manuscript.

## (F) Not checked / uncertainty log

Every changed TeX hunk was checked against the baseline and its relevant surrounding proof context. The core and syntax/arithmetic hunks were checked directly; additional independent targeted checks covered every changed hunk in Section 4, Section 6, Appendices A–D, and Section 9, including the supporting cited results. No new literature was needed or checked.

A source comparison found unchanged label sequences and unchanged citation sequences in every edited TeX file. Reference-sequence changes are the intended consolidation references and removal of the irrelevant local-connectedness lead-in. The frozen build log contains no undefined-reference, warning, or overfull-box messages. This audit did not independently render and inspect every page, re-prove every unchanged theorem, verify prior literature, or assess novelty, value, or publication positioning.

**Final self-audit.** Strongest confirmed blocker: none in the reviewed revision. Strongest suspected but unconfirmed blocker: none identified. Most important unchecked matter: independent correctness of the unchanged manuscript as a whole. The revision conclusion does not depend on unavailable material; a publication-level recommendation would require the broader checks just excluded. Final recommendation: **unknown** for publication acceptance; **no required corrections** to the reviewed revision.
