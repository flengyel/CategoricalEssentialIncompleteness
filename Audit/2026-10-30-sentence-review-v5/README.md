# (A) Kill-shots / hard blockers

The requested sentence-by-sentence terminology, definition-order, and typing audit is complete, and the confirmed findings have been corrected in the manuscript. No fatal mathematical defect was established by this scoped audit. This is an author-side review using the HostileReferee and mathematical-writing skills, not an external referee report or a certification of all proofs.

Reviewed manuscript: *Local connectedness, range functors, and essential incompleteness*, Version 5, 30 October 2026. The immutable baseline is [commit c8feb7e](https://github.com/flengyel/CategoricalEssentialIncompleteness/blob/c8feb7e8788d16418dfd1a497913b2b5a46d3670/manuscript/essential_incompleteness_via_local_connectedness_v5.tex). All source-line and PDF-page anchors in the individual reports refer to that baseline, not to the revised pagination.

Every sentence, display, heading, proof passage, source comment, and bibliography entry was read. The source was divided into seven nonoverlapping ranges covering lines 1–2347. [COVERAGE.json](COVERAGE.json) records all 188 nonblank source blocks, without gaps or duplicate assignments. These blocks record the manual reading coverage; they are not an automated proof check or an assertion that each sentence is an independent mathematical claim.

# (B) Major weaknesses

The following substantial exposition defects were confirmed and repaired:

| Baseline findings | Defect and evidence | Implemented repair |
| --- | --- | --- |
| 04-01 | §7.1 asserted disjointness and preservation of bottom without locally binding the consistency assumption. The inconsistent theory PA + (0=1) exhibits the failure of an unrestricted reading. | The subsection begins with a consistent c.e. extension of PA; the redundant later c.e. assumption is removed. |
| 04-02 | A functor with source J was attributed values at opens of X. | The text explicitly names the cosheaf and describes restriction to the three opens as a J-functor. |
| 04-03; S06-02–03 | Connectedness, defined for restriction idempotents, was applied to subfunctors; component positions had undeclared names. | Both §8.1 and Appendix A identify the connected partial identities and their indexed components. |
| M05-1 | Axiom parameters were said to range over S, although S is a functor. | The schemes, parameters, constructors, and atomic axioms are stated at each component j. |
| C05-3; P07-1 | “Split subfunctor” did not distinguish a restriction splitting from a split inclusion in the total category. | The text identifies the c.e. subfunctor on which each restriction idempotent is the partial identity and defines D_t before use. |

Each individual report contains the baseline quotation, source/page anchor, failure mode, evidence, impact, and proposed repair. These findings do not require dropping a theorem or asserting a new mathematical result. The intended consistency hypothesis is now in scope at its use.

# (C) Minor issues

All remaining confirmed local findings were addressed:

| Findings | Resolution in the revised source |
| --- | --- |
| P01-01–02 | Introduce Pfn before its functor example; state the restriction-functor and restriction-equivalence conventions in the preliminaries. |
| P02-01 | Restore the full term “restriction idempotents.” |
| P03-01 | Replace the ambiguous zero claim by the two explicit composites with a+b. |
| P03-02–03 | Replace undeclared c_M and c'_M by F_M(c) and F_M(c'); declare the numerical tagging convention. |
| P03-04 | State that represented extensions correspond to t ≥ t_0 before drawing the generic incompleteness conclusion. |
| 04-04–06 | Use the formal type ω in Rec; distinguish the coproduct isomorphism ζ from the restriction idempotent b; give the selection section's type and values. |
| 04-07–08 | Use “partial-map category,” give a context-independent Mono convention, and define R_X using actual objects obtained by the chosen operations. |
| C05-1–2 | Replace the probe/observed-carrier terminology with total morphisms H_i → Y; define U:K → Pfn and the natural isomorphism Φ_i ≅ UE_i. |
| C05-3; P07-3–5 | Use “polynomial functor,” morphisms of E or natural transformations, composites with coproduct injections, and closure under modus ponens. |
| C05-4–5 | Attribute values at X to associated cosheaves; introduce the finite-set and slice conventions before use. |
| D05-1–2 | Define τ_j = E_j(τ); reuse the particular coding and numbering from the construction; distinguish partial component functions from their total restrictions to T_j. |
| S06-01, S06-04 | Identify the representing morphisms and partial component functions; bind Y, g, and h locally. |
| S06-05–07 | Replace support language by f = dfe, retain r_1^V before its abbreviation, and refer to the first coproduct summand. |
| S06-08 | Define a frame as the family of three isomorphisms and their inverses, with Heller's citation. |
| P07-2 | Give the syntax functor's source, target, object assignment, and morphism assignment. |
| P07-6–7 | Declare the halting notation and type τ_K, its numerical extension, and the parameter morphism r; remove the local reuse of V for a numerical function. |

Established terminology was not removed merely for being specialized. Heller's “receives” and “frame” were checked against his primary text, §§6 and 3 respectively. The ordinary domain of definition of a partial function remains distinct from a restriction idempotent. Standard finite-support language for an object of the model-product category was retained; it does not introduce the undefined supported-arrow condition corrected in Appendix A.

The final source search found and corrected two repeated phrases in Appendix A beyond the individual anchor lists: “total natural maps” in the word construction and “value maps” in the range-product argument. The bibliography uses the smaller standard text size to avoid a final page containing only its last entry. No references were deleted.

# (D) Cross-section consistency failures

The repairs were checked across the main text and appendices. In particular, the same partial-identity interpretation of D_t, component convention for τ_j, generated-object definition of R_X, and frame terminology are used throughout. The section-lifting hypothesis and the counterexample to omitting it are preserved. The range-functor theorem does not acquire a product-preservation assumption.

| Baseline range | Detailed report | Reading record |
| --- | --- | --- |
| 1–295 | [Part 01](PART_01.md) | [Coverage](PART_01_COVERAGE.json) |
| 296–518 | [Part 02](PART_02.md) | [Coverage](PART_02_COVERAGE.json) |
| 519–815 | [Part 03](PART_03.md) | [Coverage](PART_03_COVERAGE.json) |
| 816–1115 | [Part 04](PART_04.md) | [Coverage](PART_04_COVERAGE.json) |
| 1116–1479 | [Part 05](PART_05.md) | [Coverage](PART_05_COVERAGE.json) |
| 1480–1907 | [Part 06](PART_06.md) | [Coverage](PART_06_COVERAGE.json) |
| 1908–2347 | [Part 07](PART_07.md) | [Coverage](PART_07_COVERAGE.json) |

The individual reports preserve their baseline diagnoses and conditional recommendations. This file records their resolution. [WRITING_REVIEW.md](WRITING_REVIEW.md) provides the actual outline, grouped comparison with the writing source, and a registry of both adequate definitions and needed repairs. The existing organization was retained.

# (E) Acceptance conditions, non-negotiable

1. **Full reading coverage:** all 188 baseline blocks assigned once, with every sentence and formula in each read. Verified in COVERAGE.json.
2. **Correction of confirmed findings:** the revised source contains the explicit types, definitions, and terminology recorded above; bounded rereading checked the changed sections and appendices. No confirmed requested-scope finding remains open.
3. **Build and rendering:** the exact revised source compiles with latexmk; the final log has no warnings, unresolved references/citations, or overfull/underfull boxes. All pages were checked in a layout overview, and the materially changed mathematical passages were inspected at readable scale. Final file identities and page count are in [VERIFICATION.json](VERIFICATION.json).

These endpoints concern the requested exposition review. Failure to meet them would leave that task unfinished; they do not constitute conditions for accepting an independently verified mathematical theorem.

# (F) Not checked / uncertainty log

This pass did not reconstruct every proof independently, formalize the paper, or repeat the earlier novelty search and verification of all bibliography claims. The scope includes local calculations and counterexamples needed to exhibit the wording defects, not a general mathematical certification.

The supplied KLR *Mathematical Writing* §1 excerpt, points 1–19, was read (printed pp.1–3; PDF pp.3–5). The request for the full official PDF timed out. Later sections, including §§4–5, were not verified in this pass; applications of the supplied excerpt and independent editorial conventions are distinguished in the writing report. Source-guided assessment beyond that verified excerpt remains provisional.

Final self-audit: strongest confirmed baseline defects were the untyped componentwise axiom parameters and the conflation of functor and cosheaf evaluation; both are repaired. Strongest suspected unconfirmed blocker: none asserted within this scope. Most important unchecked matter: independent correctness and novelty of the complete mathematical argument. Completion of the requested terminology and definition-order audit does not depend on unavailable material; full KLR source compliance is not claimed. Final recommendation: **unknown** for mathematical publication beyond this completed exposition audit.
