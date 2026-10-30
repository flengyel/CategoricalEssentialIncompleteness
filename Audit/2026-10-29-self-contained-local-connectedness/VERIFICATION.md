# Verification of the self-contained paper

Baseline: `f1b32a4df2e677bb3dd7cfabe76720bfe0a284b5`.
The source and PDF retain the basename
`manuscript/local_connectedness_and_essential_incompleteness`.

## Mathematical content and citations

The paper now contains the statements and arguments formerly supported
by the private-note citations, including the introduction's claims:

- Section 6 retains the connected-domain, partial-section, and
  range-functor inseparability proofs and includes the sufficient lifting
  criterion as Proposition 6.4 with its proof.
- Appendix A proves the three-point cosheaf comparison, categorical
  structure and range laws, universal embeddings and frames, Turing
  morphism with exact domains, and restriction-splitting comparisons.
- Appendix B constructs the finite syntax and proof diagrams, proves
  total syntax initiality, the least rule-closed theorem image, the
  one-node proof inequalities, and consistency.
- Appendix C is explicitly a counterexample to the statement obtained
  by **dropping** the lifting hypothesis. The main theorem retains that
  hypothesis. The criterion and its proof were already in the author's
  private note; the revision supplies them in this paper as requested.

The private references and bibliography entries are absent. None of their
needed arguments is replaced by a citation to another private note. The
paper uses its explicit component images and restriction splittings; it
does not invoke a free range completion. The original near-product
qualification is now attached to the sentence citing Lengyel2004 and its
corrections, with no suggestion that the qualification first appeared in
the corrections.

The mathematical-writing review read the complete integrated source;
the hostile review checks the added proofs and their dependencies.
Their reports are separate from the mathematical document. The earlier
model-family, syntactic lifting, and effective-observation proofs retain
their established content; unchanged earlier verification is reused.

## Build and rendered document

From `manuscript/`:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -outdir=../build/self-contained \
  local_connectedness_and_essential_incompleteness.tex
```

The exact revised source builds to **26 pages**. The final log contains
no warnings, undefined controls, unresolved citations or references, or
overfull/underfull boxes. All **47** explicit labels are unique and every
reference resolves. All **11** bibliography entries are cited and every
citation resolves.

All twenty-six pages were inspected in contact sheets. Readable-resolution
inspection additionally covered pages 2, 9, 15, 19, 20, and 23–25: the
near-product sentence and introduction, lifting criterion, cosheaf and
structural definitions, Turing computation and parameters, splitting
comparison, finite-proof consistency, and the conditional counterexample.
Individual construction fragments also received their recorded local
compilation and proof checks before integration.

Important locations in this PDF:

| Content | Pages |
| --- | --- |
| Introduction and near-product qualification | 1–3 |
| Lifting theorem and sufficient criterion | 8–9 |
| Three-point application | 11–14 |
| Appendix A: computational category, Turing morphism, and splitting | 14–21 |
| Appendix B: finite syntax, proofs, and consistency | 21–23 |
| Appendix C: statement with lifting dropped | 23–25 |

The source contains no private-note citation, old basename, drafting or
review commentary, “diagonal proof,” “diagonal argument,” or “Turing
compiler.” The PDF in `manuscript/` is copied from the final build.

## Artifact identity

| Artifact | SHA-256 |
| --- | --- |
| Revised TeX | `99b760671b51bafe038fa371ca9814d9de55dd53b8099487a3d6d8d44f73bc21` |
| Revised PDF | `7263f78c8e73f3c50649f8acd271b16ae9d2e25c9a84a75ecca486eb4dde6995` |
| Archived LOCOct10f source, unchanged | `039000cafbe3636ae501125d403e8fe15d42effe1c37580346d108a5bec32aab` |
| Three-point companion source, unchanged | `9323bdf98d24dba3c9de617fc18ff73cb8ce1f579f7417b34cbca5925e3c1397` |

The revised TeX Git blob is
`22ebbc0e8d7f8fcab0627abd661d1639ac17d95e`; the PDF Git blob is
`67e2a1aa9178b688162e1c7a239fa4a44d0c030b`.

Historical review reports are not overwritten. Their indexes distinguish
the earlier versions from this revision. Earlier mathematical manuscripts
and all Lean files remain unchanged by the publication tree. No Lean
audit or build is offered as verification of the paper proofs.

## Scope

The arithmetic and computational-extension conclusions are retained.
The revision supplies the explicit three-point constructions and proofs
within this paper; it does not claim new priority for arguments already
present in the author's notes. Further recursion categories and changing
presentations still require suitable effective observation functors and
compatible comparisons. The general Di Paola–Heller program is not
declared complete.
