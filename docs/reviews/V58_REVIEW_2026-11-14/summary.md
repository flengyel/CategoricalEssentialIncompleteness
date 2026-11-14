# Version 58: corrections and repeat review

Version 58 applies the v57 review's local corrections. The repeat mathematical-writing and referee reviews found no further confirmed defect in the revised passages. The outline and all 77 numbered result statements are unchanged. The current Lean record remains 69 proved counterparts and eight open results.

The revision is based on remote `main` at `98108911485679dd9e3be6775890e192e567f4d0`. Earlier full-proof review: [V57_REVIEW_2026-11-14](../V57_REVIEW_2026-11-14/review-summary.md). This review compares the edited text with that source; it does not claim another independent reconstruction of all 77 unchanged proofs or a new Lean kernel build.

## Changes

1. Corollary 4.8 specifies universal quantification in the Boolean valuation as the projection `π₂:V×2→2`.
2. Appendix B uses Appendix A's convention: the true value is the second coproduct injection. The nonexistence proof of decidable equality uses the same summand.
3. The abstract states the exact equivalence between essential incompleteness of the original theory and its constant family in the associated category.
4. The Bernardi citation now points to Sections 2–3, pp.125–128.
5. Two repeated summary sentences after Theorem 5.3 are removed; the numerical-carrier example remains.
6. Lemma 6.1's proof specifies a fixed composition program, defines its primitive-recursive index using parameterization, and explains the two trace transformations. This supplies the composition argument in the paper instead of attributing every displayed identity to the cited Montagna pages. The lemma statement is unchanged.

No publication text contains review instructions, qualifications about the review process, or claims of formalization completion.

## Outline and repeat reviews

The [outline](outline.md) records all 14 sections and 53 subsections, their roles, and the dependencies. It compares the abstract and introduction with the body. The review retains the general results before the three applications, and retains the syntax and cosheaf construction in the appendices with explicit references.

The [writing review](writing-review.md) applies the previously completed reading of all 43 sections and handouts of Knuth–Larrabee–Roberts, with relevant passages reread for this revision. It checks the revised text in reading order for defined notation, standard terminology, ambiguity, redundancy and economical exposition. The [core referee review](referee-core.md) and [application referee review](referee-applications.md) check the changed arguments and their interfaces. Lemma 6.1 received a further independent check after its trace argument was added.

All 80 numbered theorem/definition environments are identical to v57. The [result inventory](result-inventory.json) records their final numbers and page locations. The revision changes proof exposition and notation, not hypotheses or conclusions. The current correspondence table preserves all proof statuses and records the eight remaining tasks: 5.3, 8.9, 8.10, 9.6, 9.8, 10.7, 10.8 and 10.9.

## Reference audit

The reference audit covers every one of the 32 bibliography entries and all 66 citation occurrences. The [combined record](reference-audit.json) matches every original occurrence to its final source location, with primary-source evidence and qualifications. The [first report](reference-audit-a.md) covers 47 occurrences; the [second](reference-audit-b.md) covers 19. The Bernardi pinpoint is corrected and the Montagna attribution is clarified as described above. No further bibliographic correction or substantive misattribution was identified.

Source versions remain explicit. Cockett–Lack III's proposition was checked in the author preprint with journal metadata checked independently. Goguen–Burstall's mathematical passage was checked in the author report and its published identity independently. Rosolini's thesis was available in the author's identified retypesetting. Robinson–Rosolini was read in the author-uploaded original journal text. These limits are recorded per reference; no inaccessible edition is reported as read.

## Validation

- Fresh LaTeX build: 87 pages; no unresolved references, LaTeX warnings, overfull boxes or underfull boxes.
- Rendered checks cover the revised abstract, Corollary 4.8, Lemma 6.1 and Appendix B equality argument.
- All 77 numbered results and three definitions retain their statements and labels. Final page locations are recorded separately.
- The source archive contains exactly the current 24 TeX files and source guide. Archive bytes, PDF copy and manifest hashes pass the manuscript checker.
- `python3 scripts/verify.py --manuscript-only`: passed for v58.
- `python3 scripts/test_verify_axiom_parser.py`: six tests passed.
- No Lean source, dependency, challenge placeholder or permitted axiom was changed. No fresh full Lean build was run for this prose revision.

The source, PDF, archive, manifest, correspondence table, abstract copies, instructions and these reports are to be committed together to `main` and verified on the remote before completion is reported.
