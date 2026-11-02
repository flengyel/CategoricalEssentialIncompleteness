# Version 43 introduction: author-side hostile review

Scope: the revised introduction and the two new bibliography entries, read against the primary-source verification record and the stated categorical incompleteness criteria. This is a frontmatter review, not a certification of the body proofs or a journal referee report.

## (A) Kill-shots / hard blockers

None established in this scope. The historical paragraph at introduction lines 14–24 accurately separates Di Paola–Heller's criticism of axiomatized formalized Löb from their discussion of Hilbert–Bernays conditions on arithmetic provability formulas. The introduction does not claim that every construction proves effective inseparability or every formulation listed by Di Paola–Heller.

## (B) Major weaknesses

None established. The present-contribution claim is bounded by represented extension classes and by the preceding paragraphs' two arguments and explicit lifting hypothesis. Corollary 4.3 takes an inseparable pair as input; the introduction states this in its second-argument paragraph. No unsupported claim of priority or generalization occurs in the additions.

## (C) Minor issues

Anchor: the Cockett comparison, beginning “Cockett's later incompleteness theorem”. Initial wording: “a restriction idempotent on the terminal object that is neither zero nor the identity”. Failure mode: ambiguous typing. Evidence: derivation and citation. An ordinary terminal object has exactly one endomorphism, so the asserted distinction is impossible on that reading. Cockett §5.4 defines the relevant object as a partial final object, terminal only in the category of total morphisms; Theorem 7.14 uses this restriction-categorical context. Required repair: write “restriction terminal object”. This qualification was identified by the authoring agent after the initial review and is necessary for the introduction's types. Severity: local but mandatory; immediately repairable.

Anchor: introduction lines 214–226, beginning “Ramesh's introspective theories” and ending with the absence of postulated Löb/Hilbert–Bernays conditions. Claim as written: Ramesh derives Löb; the present criteria do not postulate the indicated operator. Failure mode: ambiguous positioning. Evidence: structural_argument. Both statements are individually supported, but putting the final methodological contrast in the same paragraph as Ramesh invites an assumed-versus-derived contrast that the paragraph itself correctly denies. Downstream impact: literature positioning only. Severity: minor; immediately repairable. Insert a paragraph break before “Here formula objects...” so Ramesh's result has its own paragraph and the common contribution summary follows separately. No mathematical sentence needs deletion.

## (D) Cross-section consistency failures

None established in the inspected dependencies. Section 4 constructs the sentence theory as the regular image of the sentence-conclusion morphism, assumes a partial inverse for the image monomorphism, and obtains its restriction-range representation. The interpretation proposition and comparison theorem impose their stated semantic and lifting hypotheses; the separate corollary assumes an inseparable source pair. These data support the introduction's construction/conclusion distinction.

The new CockettComputability entry is the 2014 lecture notes, not the existing 1990 CockettLists reference. Cockett–Hofstra Theorem 4.9 and Cockett's later Theorem 7.14 have distinct roles. Bernardi is credited for fixed-point and inseparability results; Ramesh is expressly credited with deriving Löb. No new categorical symbols needing types are introduced by these literature passages.

## (E) Acceptance conditions, non-negotiable

The Cockett comparison must say “restriction terminal object”; the unqualified ordinary-terminal reading is untenable. Before delivery, verify that the exact revised source compiles with the two new bibliography keys and that the rendered introduction and bibliography have no unresolved references or layout defects. Preserve Ramesh's explicit derived status and the introduction's source lifting and represented-extension qualifications. The paragraph break in (C) is the recommended local positioning repair.

## (F) Not checked / uncertainty log

The current body proofs were not audited line by line; no claim of whole-paper correctness or originality follows from this review. Primary-source conclusions were checked against the local source record and the relevant passages, including Di Paola–Heller pp. 595–596, Ramesh's introduction, and Cockett's Theorem 7.14; full sources and locators are retained in primary_sources.md. No new counterexample is needed for an editorial positioning issue.

Strongest confirmed defect: the initially unqualified “terminal object” in the new Cockett comparison; it requires the restriction-terminal qualification before delivery. Strongest suspected unconfirmed blocker: none identified in these additions. Most important thing not checked: mathematical correctness of all application proofs. The local recommendation does not depend on unavailable material. Final recommendation: unknown for acceptance of the whole paper; these frontmatter additions have no established mathematical blocker.

Resolution: the authoring agent inserted the paragraph break before “Here formula objects...”. Reinspection confirms that the absence-of-postulated-Löb/Hilbert–Bernays sentence now describes the present criteria separately; no attribution problem remains.

Additional source clarification: Cockett §5.4 (printed p. 64; cached text lines 3522–3529) explicitly defines a partial final object and notes that it is terminal in the total-morphism subcategory. Theorem 7.14 is read in that context. “Restriction terminal object” is the manuscript terminology required here.

Resolution verified: the revised Cockett paragraph now says “restriction terminal object”. This removes the ordinary-terminal typing defect.
