# Build and artifact verification

- The exact final main source and standalone appendix compile successfully. Their final LaTeX logs have no warnings, undefined references or citations, or overfull/underfull boxes.
- The main paper is 73 pages; the standalone appendix is 10 pages. Section 7.2 occupies pages 31–35; Section 7.3 and Theorem 7.6 are on page 35. Section 7.4 begins on page 36.
- The main title page and pages 31–36 were rendered and visually inspected. The new heading, theorem, equations, diagrams, page breaks, and cross-references are readable. The standalone appendix title page displays version 25.
- The 21-entry source archive passes its integrity check and includes the new subsection file and updated source-directory guide.
- The final subsection sources match the second-round review snapshots byte for byte. The first subsection has SHA-256 `1b9540d2537f6de7f658e8881d3fc9fc9c47971c1323df775762bbb20efcee45`; the second has `7cfdd66300041ad6a9fe7e59e78670d27007ed41e97fbc03ead57bf4f3840fb5`.
- The abstract, introduction, and modular Appendix A match the version-24 baseline byte for byte. The standalone appendix source changes only its visible version and PDF title metadata.
- The mathematical-source scan found no editorial, review, process, or LLM commentary.
- The original theorem statements and proof steps are preserved, apart from the explicit imports and corrected predicate terminology. No new literature claim or bibliography entry was introduced.
- No Lean code was changed or verified. The review disposition concerns the two revised subsections and their inspected dependencies.

## Artifact SHA-256 before upload

- `logical_consequence_and_essential_incompleteness_v25.pdf`: `c39fc2b82d58dbf3ad09cec42d831f2b3e8443a732d2f8715206dfba0eeb40e2`
- `logical_consequence_v25_source.zip`: `cd518df2d15430449868356e754fd520d90a3ad5b30c87fc9bb9a0e71fde18fd`
- `first_order_syntax_and_deductive_closure_appendix_v25.pdf`: `e401097216bd57aa122f8b8a1cce8a31c9a55af40fc52b65f8fc7bd95d0b80e1`
- `first_order_syntax_and_deductive_closure_appendix_v25.tex`: `53a0420044494913b1e78cb9feef27b0c01794b711e1427e599f99b74e2ee112`
