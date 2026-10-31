# Version 7: Miller application, mathematical prose, and proof objects

Reviewed manuscript: [Local connectedness in recursion categories and essential incompleteness](../../manuscript/essential_incompleteness_via_local_connectedness_v7.pdf)
([source](../../manuscript/essential_incompleteness_via_local_connectedness_v7.tex)),
31 October 2026, 35 pages.

The manuscript adds the Miller-sequence application to the version 5 paper
and revises the abstract, introduction, and exposition throughout. The new
Appendix B.3–B.4 characterizes derivation trees by initiality and sentence
proofs by pullback. All concrete findings in the reports below have been
resolved in the inspected final source. The reports record their individual
scope; they do not certify the manuscript by formal verification.

## Mathematical changes

Section 4 constructs a recursion category of partial numerical functions
computed with the same domain and values from every binary name of Miller's
sequence. It proves inseparability of the sequence's strict-cut pair by an
ordinary recursive reduction from the categorical diagonal pair. Every fixed
binary name nevertheless computes a separator. The resulting real-closed-field
theory is essentially incomplete relative to the specified notion of
semidecidability. The sequence is attributed to Miller (2004), Theorem 6.3;
the binary-name formulation is cited to Bauer and Hanson, Section 2.1 and
Theorem 2.2. The weaker proposed application concerning adjoining partial
maps is not included.

Appendix B.3 defines the axiom-instance object, the pullback matching the two
premises of modus ponens, and an endofunctor on the slice over formulas.
Finite proof trees form its initial algebra. The proof verifies effective
evaluation, conclusion preservation, naturality, and uniqueness.

Appendix B.4 gives the corresponding first-order construction with axiom,
modus-ponens, and generalization rules. Nonlogical axioms are sentences.
Derivations with arbitrary formula conclusions form the initial algebra;
sentence proofs are obtained by pullback along the sentence subobject.
The theorem restriction idempotent is the range of the conclusion map in
the relevant partial-map category. In the Miller case, evaluation first
tests membership in the valid-tree carrier to obtain exactly the required
domain. No general existence of W-types or proof objects in every recursion
category is asserted.

Other repairs make arrow types, quantifiers, and restriction preservation
explicit. They include the section-lifting equations, the formal numerical
types in the pair functor, the two-variable domain of the endpoint evaluator,
and preservation of restrictions by the splitting equivalence.

## Writing and mathematical reviews

The mathematical-writing plugin supplied the complete-source workflow.
Knuth, Larrabee, and Roberts's *Mathematical Writing* was the governing
source; Heller's *An Existence Theorem for Recursion Categories* (1990)
provided the requested model of mathematical exposition. The revisions
remove repeated announcements, unquantified generalities, duplicated
definitions, and conclusions that repeat the preceding equation. Necessary
distinctions concerning domains, uniformity, and source and target categories
remain explicit.

The hostile-referee plugin was applied in three assigned parts, followed by
a separate audit of the new proof-object constructions. Historical findings
and their source-line anchors remain in the reports, with final dispositions
identifying the completed repairs.

- [Complete-source writing review and paragraph inventory](WRITING_REVIEW.md)
- [Hostile review of Sections 1–4](HOSTILE_SECTIONS_1_4.md)
- [Hostile review of Sections 5–9](HOSTILE_SECTIONS_5_9.md)
- [Hostile review of Appendices A–C and the bibliography](HOSTILE_APPENDICES.md)
- [Final audit of the proof-object characterizations](PROOF_OBJECTS_REVIEW.md)

The original prose review used the delivered version 6 source. Its SHA-256
is recorded below. Version 7 incorporates those revisions and the subsequent
proof-object additions. The version 6 line references in the reports are
historical references, not assertions that the quoted wording remains.

## Verification

The exact version 7 source compiled with `latexmk -pdf`, with no unresolved
references, LaTeX warnings, overfull boxes, or underfull boxes in the final
log. The resulting 35-page PDF was rendered in full. All pages were inspected
in contact sheets; the title, introduction, and new categorical diagrams on
pages 30–32 were also inspected individually. No clipping, overlap, or missing
diagram labels was found.

No Lean source was changed or tested in this update. The repository's current
formalization is indexed to version 5. The Miller application and the new
initial-algebra statements are not claimed to be formalized.

Build from `manuscript/` with:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error essential_incompleteness_via_local_connectedness_v7.tex
```

This commit changes the manuscript, its PDF, the two manuscript indexes, and
these review records. Existing Lean work and older manuscripts are retained.

## Artifact hashes

SHA-256 values for the reviewed files are supplied in
[ARTIFACT_HASHES.json](ARTIFACT_HASHES.json).
