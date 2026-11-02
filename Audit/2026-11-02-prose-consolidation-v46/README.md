# Version 46: prose and consolidation

Revision dated 2 November 2026 of *Logical consequence and essential incompleteness in recursion categories*. The review applies the mathematical-writing skill under Knuth--Larrabee--Roberts and the hostile-referee skill. These are author-side reviews, not independent peer review.

## Changes

- Lemma 6.2 invokes Lemma 5.2 for the total functional graph instead of repeating witness search. The graph, its typing, and the model-wise unique-section argument remain.
- Appendix D.2 invokes Corollary 6.3 for the model-family inseparable pair. The extension functor and its preservation and Turing-factorization arguments remain.
- The Miller conditional uses Propositions 3.4 and 8.2. Its branch equations and single-program requirement across representations remain.
- Section 9 cites Appendix B for the cosheaf non-equivalence and endpoint calculation. The parameter-map proof remains. The unused local-connectedness lead-in is removed.
- Appendix B refers to Appendix A for regularity and regular images. Appendix A retains the prerequisites required for its independent categorical construction. Its list object remains in Appendix A; the application sections retain their separate realization proofs.
- Removed empty qualifiers, duplicated proof recaps, and the adjective “raw.” Short formulas are inline by default; displays remain where they aid reading or supply numbered equations or diagrams.

## Review records

- [Core prose edits](core_edits.md)
- [Syntactic and model edits](syntax_edits.md)
- [Application edits](application_edits.md) and [three-point edits](threepoint_edits.md)
- [Appendix A edits](appendix_edits.md)
- [Final consolidation](root_final_edits.md)
- [Hostile-referee review](hostile_review.md)
- [Mathematical-writing review and resolution](final_writing_review.md)
- [Final source invariants](final_invariants.json)
- [Build and artifact validation](validation.json)

## Validation and scope

The final 22 TeX files and README match the 23 source-archive members. All labels, citation keys, and numbered equation bodies are preserved. The three unchanged TeX files are the assembly, abstract, and bibliography. Nineteen TeX files have prose, display, consolidation, or version/date changes.

The final source builds without warnings to 74 pages, compared with 78 in version 45. Unnumbered display blocks decrease from 325 to 244. All pages were inspected through seven contact sheets, with selected critical pages inspected at full resolution. No layout issue was found.

The reviews cover the complete prose and the mathematical dependencies of the consolidations. They do not constitute a new verification of every unchanged theorem or citation. Required corrections from the reviews were applied and rechecked. The validation record identifies the exact final source and artifact hashes.
