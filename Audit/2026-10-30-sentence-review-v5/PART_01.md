# (A) Kill-shots / hard blockers

None confirmed within the requested terminology, definition-order, and typing scope. This is an author-side audit of *Local connectedness, range functors, and essential incompleteness*, Version 5, at commit `c8feb7e8788d16418dfd1a497913b2b5a46d3670`. Every sentence, display, heading, and source line in baseline lines 1–295 was read, including the abstract, introduction, related work, and categorical preliminaries. The coverage record contains B001–B031.

# (B) Major weaknesses

None confirmed in this portion. The abstract correctly states the categorical lifting result before its logical application. It does not identify categorical inseparability with the logical incompleteness statement. The introduction identifies the non-locally connected source, the locally connected target, the preservation conditions, and the role of the section-lifting condition. Familiar concepts may be previewed here before their formal definitions.

# (C) Minor issues

**P01-01 — The local notation for the category of partial functions is explained after its first formula.** Anchor: PDF p.3, §2.2, baseline lines 254–262, B027: `F:Pfn→Pfn`, followed at the end of the example by “Here Pfn denotes the category of sets and partial functions.” Failure mode: `missing_definition` (late, not absent). Evidence: `absence_in_text` at the first formula, with the explanation present later in the same paragraph. The mathematical example is understandable, but its notation can be introduced without making the reader look ahead. Severity: minor. Repair: move “Let Pfn denote the category of sets and partial functions” before the example's functor signature. Downstream impact: reading order only; no hypothesis or calculation changes.

**P01-02 — State the restriction-equivalence convention in the preliminaries.** Anchor: PDF p.1, abstract and introduction, baseline lines 48 and 118–119; formal use in §8 and Appendix A.5. The text says “restriction-equivalent” and “equivalent as a restriction category,” but the preliminaries define range functors without separately giving the preservation condition for a restriction functor or the equivalence convention. Failure mode: `missing_definition` within the requested self-contained convention audit. Evidence: `absence_in_text`, after whole-source search. These are established categorical notions; their use is not invented terminology or evidence of a false theorem. Severity: minor. Repair: after the total-arrow subcategory, define a restriction functor by preservation of the restriction operation, and define a restriction equivalence by restriction functors in both directions with composites naturally isomorphic to the identities. Downstream impact: makes the later comparison invariant's categorical scope explicit. Abstract previews remain in place.

Two further local clarifications were made without classifying standard shorthand as a mathematical defect: the definition of a restriction category now expressly starts with an underlying category, and the connectedness definition expressly types all three restriction idempotents on the same object. The already defined term “total arrow” replaces the unnecessary adjective in “total test arrows” later in §6.

# (D) Cross-section consistency failures

No additional confirmed failure in this portion. The following distinctions were checked and retained:

| Item | Status |
| --- | --- |
| Composition `gf` | Its order is declared before the restriction axioms. |
| Restriction idempotent, totality, order, meet, join, zero, disjointness, complement, inseparability | Defined in §2.1 before the formal applications. |
| Inverse image and range | Typed before use. The range agreement law is explicitly imposed. |
| “Receives” | Defined by `rf=f`; verified against Heller (1990), §6, printed p.1261. A citation was added. This is established terminology and was retained. |
| Restriction splitting | Objects, arrows, identities, and totality are explicitly given. The equation `f=dfe` is available for the later support-language repair. |
| Binary restriction products and coproducts | Their morphisms and equations are stated; no terminal object is added to the binary-product convention. |
| Range functor | Source, target, covariance, preservation properties, and the canonical coproduct comparison are explicit. Product preservation is not assumed. |
| Connectedness | Defined for restriction idempotents. The later application of this adjective to subfunctors is recorded in Parts 04 and 06 and corrected there. |
| Turing morphism | Its type, quantifiers, total parameter morphism, and equation are explicit. |
| `S`, `S_T`, and primed variants | The introduction distinguishes uniform provable equality from the pointwise variant and gives the reason for excluding the latter. |
| Three-point space | Described as two Sierpiński spaces glued along their open singleton, not as the two-point Sierpiński space itself. |
| Heller's frame | Verified separately against Heller (1990), §3, printed p.1256. The family terminology is corrected in Part 06; no finding claims the word is invented. |

# (E) Acceptance conditions, non-negotiable

1. Move the `Pfn` explanation before the first functor formula. Endpoint: the example reads in definition order. This is a local editorial condition, not a reason to reject the theorem.
2. State the restriction-functor and restriction-equivalence conventions before their substantive use in §8. Endpoint: the comparison has an explicit categorical meaning. No new mathematical hypothesis is required.

# (F) Not checked / uncertainty log

The complete assigned text and the relevant later occurrences were read; no new general correctness or novelty audit was attempted. The reference claims in the introduction were not all researched again in this terminology pass. Heller's uses of “receives” and “frame” were checked in the available primary-source text. The supplied KLR *Mathematical Writing* §1 excerpt, points 1–19 (printed pp.1–3; PDF pp.3–5), was consulted. Points 11, 14, and 17 support introduction of variables, consistent notation, and readable ordering. The request for the full official PDF timed out, so later advice, including §§4–5, is not represented as verified in this pass. The report format and explicit typing convention are the review method, not attributed to KLR.

Final self-audit: strongest confirmed blocker: none; strongest local finding: P01-01's late notation explanation. Strongest suspected unconfirmed blocker: none identified within this scope. Most important unchecked matter: independent correctness and novelty of the complete manuscript. These local findings do not depend on unavailable material. Final recommendation: **unknown** for mathematical publication; the two local editorial conditions are resolved in the revised source.
