# Mathematical-writing review — manuscript v57

The existing organization should be retained. The complete reading found one inconsistent truth-value convention and one underspecified valuation operation. A short abstract clarification would remove an ambiguity already resolved in the introduction. None requires a new section or a wholesale rewrite of the abstract or introduction.

Source: *Logical consequence and essential incompleteness in recursion categories*, version 57, 10 November 2026; repository revision `dfe6d3b9b948875d9d268ef8bbd332d65c6b53e5`. All manuscript source anchors below are relative to `manuscript/latex/`. Page numbers refer to the supplied PDF; printed and PDF page numbers coincide. This review does not change the current Lean record: 69 of 77 results are recorded complete, and eight remain open. No Lean build was performed by this reviewer.

## Current outline

The full section/subsection outline, each unit’s function, the main dependency table, and the sentence/paragraph comparison with the body are in [functional-outline.md](functional-outline.md). It contains all 14 sections and 53 subsections in their actual input order. The nested title in §9.2 is “The index sets below and above 1/2”; the preliminary regex outline truncated it at `\texorpdfstring`.

The paper proceeds from computational comparison (§3), through internally generated theories and adjunctions (§4), to their associated categories (§5). Sections 6–7 construct the syntactic realization and its sound interpretation. Sections 8–10 supply arithmetic, Miller and cosheaf applications. Appendix A defines the syntax and deduction construction, Appendix B supplies the cosheaf category, Appendix C establishes the need for lifting, and Appendix D supplies the faithful family of model interpretations. These forward references are explicit. The proof dependencies do not require relocating the appendices.

## Source principles used

The supplied Stanford report by Donald E. Knuth, Tracy Larrabee and Paul M. Roberts was read in full, including all 43 sections, exercises, solutions and handouts. Its printed pages are used here, not the report’s PDF page count. The extraction has OCR defects in some scanned handouts; no exact quotation or fine-grained disputed wording from those portions is relied upon.

- §1 points 10–13, printed pp2–3: connect formulas by explanatory prose, give complementary descriptions, consider what the reader knows next, and retain readable prose when formulas are skimmed.
- §1 point14, printed p3: keep notation consistent for the same concept.
- §1 point17, printed p3: avoid left-to-right ambiguity.
- §1 point24, printed p5: the opening should be direct and carefully composed.
- §1 point26, printed pp5–6: avoid needless jargon and noun clusters.
- §§4–5, printed pp9 and12: definition placement is contextual; introduce symbols informally or define them near use, rather than imposing a rigid definition-first dictionary.
- §27, Herb Wilf, printed pp59–60: say what the work does up front and let theorem statements serve skimming readers; useful motivation need not be long.
- §32, Leslie Lamport’s handout, printed p71: remove prose about selecting or presenting material when it contributes no mathematics.
- §37, printed pp90–93: keep terminology consistent, do not define unused notions, and make forward proof dependencies clear.
- §40, printed pp100–102: automated diction or readability flags are prompts to inspect context, not verdicts. This rules out mechanical removal of technically meaningful words.

The report format and priority labels below are editorial choices, not a format prescribed by the book.

## Findings and proposed actions

| Priority | Location | Confirmed difficulty | Principle and concrete action |
|---|---|---|---|
| Necessary notation correction | `appendices/b-three-point-cosheaves.tex:568–570,594`, p80 | Appendix A fixes the first injection of `2=1+1` as false and the second as true, and decidable equality has true inverse image equal to the diagonal. Appendix B switches to the first summand without announcing a new convention. The nonexistence proof works after either convention, but the paper should use one. | §1.14 and §37, consistent notation. Delete the repeated definition at568–570 and invoke Appendix A’s convention. At594 replace “first summand” by “second summand.” |
| Necessary construction clarification | `sections/03b-internal-adjunctions.tex:350–353`, p14 | “Quantification by `V×2→2`” names a type but not a morphism. The argument needs the second projection, so quantification leaves the Boolean value unchanged. | §1.11, define introduced data; supplementary typing requirement. Replace that clause by “and universal quantification by the projection `\pi_2:V\times\Two\to\Two`.” This does not change the proof. |
| Recommended abstract clarification | `abstract.tex:14–16`, p1 | “Passage to the corresponding internal theory” does not say which construction is meant, and the original theory is already internal. Introduction lines64–79 and §5 correctly locate it. | §1.17, ambiguity; §27, tell the reader the result. Replace the sentence by the exact wording below, which names the constant family and associated category. |
| Optional deletion | `sections/04-theory-extensions.tex:242,246–247`, p17 | The first and last sentences repeat general claims already made and proved. The intervening numerical-carrier example has content and should remain. | Lamport §32: remove non-contributing summary prose. Delete only “The construction retains the theory inclusion and sentence operations.” and “The theorem and refutation subobjects determine the incompleteness assertion of Theorem5.3.” |

The first two findings are local writing/notation repairs, not newly identified false theorems. The abstract repair is recommended because it resolves a genuine referent ambiguity. The closing-sentence deletions are optional; they provide no reason to reopen the overall organization.

## Exact replacement wording

### Appendix B convention

Replace the paragraph at lines568–570 by:

```latex
Decidable equality has the meaning fixed in
Appendix~\ref{app:categorical-hypotheses}: it is a morphism
$\epsilon:V\times V\to\Two$ in $\mathcal E$ whose inverse image
of $\mathbf t:1\to\Two$ is the diagonal.
```

At line594 use:

```latex
$\epsilon_1(r_1^Vu,r_1^Vv)$ lies in the second summand.
```

### Corollary 4.8 valuation

Replace the end of lines350–352 by:

```latex
Interpret the nullary predicates by $d$, equality by
$\mathbf{t}$, negation and implication by their Boolean truth
functions, and universal quantification by the projection
$\pi_2:V\times\Two\to\Two$.
```

### Abstract

Replace lines14–16’s sentence by:

```latex
A consistent theory containing a fixed global logical theorem is
essentially incomplete if and only if its constant family in the
associated category is essentially incomplete.
```

This is the construction `B_U` defined at §5.3. “Constant family” is ordinary categorical terminology, used here with its ambient category specified; no symbol is needed in the abstract.

## Definition order and terminology audit

| Notion | First preview / explanation | Formal introduction and use | Verdict |
|---|---|---|---|
| Restriction idempotent/domain | Introduction lines11–14, p1 | §2.1 lines7–21, p4 | Proper preview and definition. “Domain” is attributed to recursion-category terminology, not invented. |
| Restriction order, disjointness, complementary pair, inseparability | Introduction lines26–29, p2 | §2.1 lines32–47, p4 | Introduced before the comparison proofs. |
| Range functor | Introduction lines30–32, p2 | §2.2 lines132–147, p5 | Definition explicitly includes restrictions, ranges, zeros and coproducts; non-preservation of products is exemplified. Retain. |
| Recursion/Turing category | Abstract and introduction preview | §2.3 lines166–190, pp5–6 | Appropriate familiar preview for intended readers; no elementary definitions needed in the abstract. |
| Sentence theory, consistency, completeness, essential incompleteness | Introduction lines17–29 | §4.1 lines11–43, pp8–9; Appendix A after TheoremA.6 | Consistent descriptions. Appendix A supplies the underlying generated image. |
| Logical translation | Introduction lines49–52 | §4.4 (`03b`) lines61–93, p11 | Object/morphism types, rule witnesses and composition stated. |
| Associated category | Introduction lines64–65 | §5.1 lines23–30, p15 | Partial spans and their slice equation stated before use. |
| Stable under parameters | Abstract preview; §4 hypotheses | Appendix A lines147–154, p68 | Precisely defined; explicit forward references are sufficient. |
| Initial derivation algebra | §4.1 names conclusion morphism and points to Appendix A | Appendix A lines415–479, pp71–72 | Underlying rule-object construction and least-image argument supplied. |
| Numerical codes vs objects | §6 fixes `|X|`, `gamma_X`, graph indices and quotient classes | §6.1 and §8.4 (`08c`) lines20–27 | Distinctions explicit. There is no justification for removing coding detail needed by later comparison. |
| “Frame” | §10 lines109–114, p59 | Three specified isomorphisms with citation to Heller; LemmaB.6 constructs them | Defined technical term with a mathematical role. Retain. |
| c.e. subfunctor | §10 lines58–63, p58 | Component carriers and transition restrictions explicitly given | Defined descriptive term, not a substitute for construction. |
| “Proper” theory inclusion | §5.2 line104, p15 | Proof lines143–145 proves that an isomorphism would force a section; §10.9 says “not an isomorphism” | Familiar proper-subobject usage, but “not an isomorphism” could replace it if desired. Not a necessary new definition. |
| True/false coproduct convention | Appendix A lines37–38 and137–146 | Appendix B lines568–594 reverses it | The one confirmed convention inconsistency; repair above. |

The entire TeX was also searched for the earlier offending expressions and for process-oriented replacements. “Option-valued,” “failure tag,” “success value,” “source derivation algebra,” “raw,” “actual,” “pipeline,” “checkpoint,” “workflow,” “universal program” and “evaluator” are absent from the publication text. The occurrences of `tag_n` are explicit primitive-recursive coproduct-code maps in Lemma6.8, not the undefined phrase “failure tag.” “Canonical” accompanies specified product/coproduct comparisons or inclusions; “ordinary” in Appendix C distinguishes unrelativized computation from computation relative to K; “standard” distinguishes natural-number codes from nonstandard model elements. These occurrences have mathematical work and should not be deleted mechanically.

No further missing local definition, inconsistent referent or empty qualifier was confirmed in the full reading. Repeated constructions in the numerical, Miller and fork applications discharge different effective and parameter-preservation hypotheses. They are not duplicates merely because their finite-tree inductions have the same shape. The long numerical comparison supplies actual inverse coding maps; replacing it by an unsupported “similarly” would remove proof content.

## Outline and front-matter verdict

The abstract covers the contributions and restrictions of the body. The introduction states the two incompleteness criteria separately, keeps the arithmetic signed theory distinct from the ordinary arithmetic-extension application, and places the three specializations in the later example sections. It does not reproduce the proofs or move the examples into §5. Its roadmap matches the nested input order. The related-work paragraphs assign each citation a role; none is removable merely because it is contextual rather than a proof dependency.

Retain the current outline. Apply the two necessary local repairs and the one abstract clarification. The two optional closing-sentence deletions may be made in the same revision; no section restructuring is warranted by this review. The introduction packages categorical and internal-theory conclusions under a sufficient hypothesis; its categorical assertions are already supported by §5.1–5.2 without the additional syntax assumptions, so no replacement paragraph is proposed.

## Actual reading scope

Read completely: the skill and both supplementary reference files; the supplied 5,729-line KLR extraction (all 43 sections and handouts); all 24 current LaTeX files, including preamble, abstract, every section and nested input, all appendices and bibliography. Total main section/appendix source reviewed: 7,579 lines, plus front matter and bibliography. The current source was compared with the literal outline and result inventory, and relevant passages were located in the supplied PDF extraction.

No manuscript edit, TeX compilation or new kernel build was performed by this reviewer. No claim about the novelty of a result or every external source’s correctness is made by this writing review; the existing literature assertions were checked for their explanatory role and specificity, not re-researched here. The parent review’s independent mathematical and source checks remain separate evidence. The proposed replacements were checked for preservation of the mathematical hypotheses and conclusions.
