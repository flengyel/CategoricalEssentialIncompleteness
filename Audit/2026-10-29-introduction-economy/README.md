# Version 2: categorical essential incompleteness

[PDF](../../manuscript/archive/essential_incompleteness_via_local_connectedness_v2.pdf) · [LaTeX source](../../manuscript/archive/essential_incompleteness_via_local_connectedness_v2.tex)

Version 2 is dated 29 October 2026 and has 27 pages. The filename and title-page version distinguish it from the preceding cached PDF. The previous unversioned files remain historical copies; active README links point to Version 2.

## Mathematical dependency

- Theorem 6.3, page 8, is the range-functor lifting theorem. Products are formed in its source before applying the functor; product preservation is not a hypothesis.
- Proposition 6.4, page 9, proves the sufficient lifting criterion using disjoint-arrow joins.
- Corollary 6.7, page 10, pulls a hypothetical separator of theorem/refutation domains back to a separator of the categorical inseparable pair. Its conclusion is inseparability of those domains, with incompleteness as a consequence.
- Corollary 7.1, page 11, uses J:Rec→Pfn and actual proof-conclusion ranges and numeral substitution in Split(Rec). It proves recursive inseparability of every consistent c.e. extension's theorem/refutation sets and hence essential incompleteness of PA. The model-family functor F_T is a separate application of Theorem 6.3.
- Theorem 8.2, pages 15–16, uses the coproduct-summand pair supplied by Theorem 6.3 for the three-point recursion category. Its positive and negative atomic axioms use that same pair. The internal incompleteness proof applies Corollary 6.7; endpoint recursive inseparability is an additional instance of Theorem 6.3.

## Reviews and implemented repairs

The [completion outline](COMPLETION_OUTLINE.md) records the argument before final revision. The [mathematical audit](FINAL_HOSTILE_REVIEW.md), [writing audit](FINAL_WRITING_REVIEW.md), and [focused categorical-bridge check](CATEGORICAL_BRIDGE_REVIEW.md) identify their reviewed snapshots and scope. Earlier files in this directory record the initial introduction/antecedent pass, including the temporary pause while the arithmetic dependency was checked; they are not the final disposition.

The final source distinguishes the syntactic F_T instance from the numerical J instance, defines the remaining local notation before use, names the theorem whenever lifting is removed, and uses one pair throughout the three-point incompleteness argument. All needed local-connectedness, lifting, three-point, splitting, syntax and proof arguments remain in the body or appendices. No private-note citation substitutes for those arguments. The original near-product qualification remains beside the Lengyel 2004/errata citations.

After the reviewers' snapshots, the parent read the final changes: the numerical pair is defined directly in Rec; regularity, extensivity and decidable equality are defined before their propositions; a redundant endpoint recap is replaced by a precise sufficient extension statement. These changes preserve the checked proofs. No confirmed mathematical defect remains from these reviews. Novelty and external peer-review acceptance were not certified. No Lean files changed or Lean verification was claimed.

## Build and rendered check

From `manuscript/`:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=../build/version2 \
  essential_incompleteness_via_local_connectedness_v2.tex
```

The exact source was compiled to convergence. The final log has no warnings, unresolved references or citations, or overfull/underfull boxes. A 27-page visual overview was inspected; pages 1–2, 10–11 and 15–16 were also inspected at readable resolution. The overview shows no clipped or blank pages. The title page displays Version 2, the introduction has the original near-product qualification, and the inspected corollaries show the stated dependency.

| File | SHA-256 |
| --- | --- |
| `essential_incompleteness_via_local_connectedness_v2.tex` | `afa9ea49e8de7aeaae35b0ba430edab9aaaf04b2fcc36c476c4b7793fac17171` |
| `essential_incompleteness_via_local_connectedness_v2.pdf` | `f24f33c765478ab02c96743658560e977b29baf1c0125caf6bbfd2937b8dc4b6` |
