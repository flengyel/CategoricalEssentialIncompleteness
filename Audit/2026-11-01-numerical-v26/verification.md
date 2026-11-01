# Build and artifact verification

- The final main source and standalone appendix compile successfully. Their final LaTeX logs have no warnings, undefined references or citations, or overfull/underfull boxes.
- The main paper is 77 pages and the standalone appendix 10 pages. Section 7.4 occupies pages 36–41; Section 7.5 occupies pages 41–42. Section 7.6 begins on page 42.
- The main title page and pages 36–43 were rendered and visually inspected. Pages 40–41 were rendered again after the final local wording change. The diagrams, equations, comparisons, and subsection boundaries are readable. The standalone appendix title page displays version 26.
- The 23-entry source archive passes its integrity check and includes both new numerical subsection files and the updated source guide.
- All three final arithmetic files match the round-5 review snapshots byte for byte. The realization file has SHA-256 `f6606bf81ca7546b1065ae10e80e68482000ff27add2485af36ff504e879f448`; the numerical incompleteness file has `11d6c06139fa1b2b457d3c1a577026767afae0cd2121005eac5c3ef1ed9d98f8`.
- The abstract, introduction, modular Appendix A, and Sections 7.2–7.3 match the version-25 baseline byte for byte. The standalone appendix source changes only its displayed version and PDF title metadata.
- The mathematical-source scan found no editorial, review, process, or LLM commentary. No new literature claim or bibliography entry was introduced.
- No Lean source was changed or checked. Review acceptance is scoped to the revised numerical subsections and their inspected dependencies.

## Artifact SHA-256 before upload

- `logical_consequence_and_essential_incompleteness_v26.pdf`: `019fcc91b0773e3945eec2b91607d452e10d1f75a6b73286b939b347b5e97a28`
- `logical_consequence_v26_source.zip`: `4cb28377251171dfb878ecc7fc4f76076040a34d780bffd836d05bae716a7936`
- `first_order_syntax_and_deductive_closure_appendix_v26.pdf`: `f42c0a22646040381f5c8c7815356f61c3bc16abcfeadcd261d925644d9e6bdf`
- `first_order_syntax_and_deductive_closure_appendix_v26.tex`: `b853a321c0457c4190abdeefe8fef24602bcbea998aa70adb1c4d00a0014c219`
