# Mathematical writing review

The note contains no LLM-facing instructions, drafting history, review claims, or other editorial-process remarks. Its paragraphs introduce the mathematical problem, define structures, prove claims, or establish the arithmetic instance. The main prose change needed is to state the computably enumerable restriction on extensions explicitly in the abstract. Several local expressions can also be made more direct. The mathematical qualifications about partial maps, stable unions, and an arbitrary base theory should remain.

Reviewed work: Florian Lengyel, *Deduction and essential incompleteness in recursion categories*, dated 29 October 2026, nine pages, repository commit `a9da9ee538edbf4a57e4469185f014aa88c5daf8`. All line references below refer to its 669-line LaTeX source, SHA-256 `8b5a92b888bd08bb627e5280442c6fb45dc5172726905b618fe58f72f6ce07c0`. The accompanying PDF has SHA-256 `55dfc6924aded66f7becc4477801c5f7b6f2e09b8afc240e65f94c5611e0d3c9`.

## Current outline

The central question is how partial rule morphisms produce deductive closure on domains, and which additional representation condition forces every consistent closed extension to be incomplete. The contribution claimed in the text is a conditional categorical construction and its arithmetic realization.

| Existing section | Function and contents | Principal result and prerequisites |
| --- | --- | --- |
| Abstract, p. 1 | States the closure construction, inseparability implication, and arithmetic consequence. | Previews Theorems 3.1, 4.2, and 4.3 and Corollary 5.2. |
| 1. Domains and ranges, pp. 1–2 | Fixes composition, partiality, restriction products, domains, domain order, and universal ranges. Defines direct and inverse image. | Definition 1.1 and Lemma 1.2 yield the covariant functor \(E_!:\mathscr R\to\mathbf{Pos}\), the local direct/inverse-image inequality, and the adjunction for total maps. |
| 2. Stable unions and inverse image, pp. 3–4 | Defines Heller stable unions. Proves their behavior under meet, direct image, total inverse image, and finite powers of increasing chains. Declares the contravariant domain functor before its assignments. | Lemmas 2.2 and 2.3 use ranges and the specified stable unions. With finite stable unions, \(E:\operatorname{Tot}(\mathscr R)^{op}\to\mathbf{BDLat}\). |
| 3. Deductive closure and theories, pp. 4–5 | Describes supported rule morphisms, range images of premise domains, deduction stages, selected conclusions, and theories as closure-fixed domains. | Theorem 3.1 uses ranges, finite stable unions, finitely many finitary rules, and stable unions of their generated stage chains. Definition 3.2 specifies extensions by \(b\le t\). The reflector onto closed domains is left adjoint to inclusion. |
| 3.1. Morphisms of presentations, p. 5 | Defines \(\mathsf{Cons}\), supported maps satisfying the closure inequality, the contravariant functors of domains and theories, and their natural inclusion. | Inverse-image functoriality and the defining closure inequality establish the construction. |
| 4. Representation and essential incompleteness, pp. 6–7 | Defines a negative domain, consistency, completeness, complementary pairs, separators, and representation through \(\sigma\). Proves inseparability, essential incompleteness, and inheritance of representation. | Theorem 4.2 uses representation and the total-map inverse-image calculus. Theorem 4.3 adds the presentation of theories from Theorem 3.1 and excludes a complementary separating extension. |
| 5. The arithmetic realization, p. 7 | Identifies domains and ranges in the category of partial recursive maps. Proves stable unions for uniformly c.e. families and gives a counterexample to arbitrary countable increasing joins. | Proposition 5.1 supplies the unions needed by the arithmetic stage construction. |
| 5.1. Effective deduction, p. 8 | Chooses effective syntax and a Hilbert calculus. Gives modus ponens and generalization as partial recursive rule maps. Verifies uniformity of stages and identifies closure-fixed sentence domains with c.e. theories. | Theorem 3.1 and Proposition 5.1 identify the generated closure with derivability. The mentions of \(Q\) and PA concern this closure identification. |
| 5.2. Representation and arbitrary base theories, pp. 8–9 | Defines syntactic negation and total numeral substitution. Defines strong numeralwise representation and derives the categorical equations. Transfers representation from an arbitrary base to a c.e. extension. | Corollary 5.2 assumes strong numeralwise definability in the base; consistency and effective syntax give the categorical instance for each c.e. extension. |
| References, p. 9 | Identifies Di Paola–Heller, Heller, and Cockett–Lack as structural sources. | No standalone historical comparison with the Di Paola–Heller program appears in the note. |

The order follows the mathematical dependencies. No rearrangement of sections is recommended for this prose task.

## Source consultation

The supplied copy of Donald E. Knuth, Tracy Larrabee, and Paul M. Roberts, *Mathematical Writing*, was read in §1 (printed pp. 1–6; PDF pp. 3–8), §§4–5 (printed pp. 9–13; PDF pp. 11–15), and §31 (printed pp. 69–71; PDF pp. 71–73). The source is the report based on the 1987 Stanford course. Its Library identifier is `libfile_53ef001c39508191895fe913d122fc16`, filename `knuth_mathematical_writing.pdf`. Direct attempts to retrieve the official Stanford PDF timed out; the supplied copy provided the relevant text.

Verified principles used here are: self-contained theorem statements (§1, point 5); connected exposition and complementary explanations (points 10–11); reader motivation (point 12); prose that remains readable when formulas are skimmed (point 13); unambiguous sentences (point 17); and avoiding needless jargon (point 26). Sections 4–5 allow judgment about the placement of definitions and preserve useful proof signposts. The remarks about examples and treating the underlying idea rather than merely polishing its wording in §31 are Leslie Lamport's, recorded by the report's authors. The prohibition on editorial-process and LLM-facing remarks is the Mathematical Writing plugin's supplementary requirement, not a rule attributed to this historical source.

## Findings and concrete actions

| Manuscript anchor and actual wording | Difficulty | Basis | Recommended action |
| --- | --- | --- | --- |
| Abstract, p. 1, lines 39–41: “The arithmetic instance gives essential incompleteness for every consistent theory strongly defining all recursive sets numeralwise; the base theory need not be computably enumerable.” | The abstract leaves the c.e. restriction on extensions implicit, although the base may be arbitrary. A reader may mistake the quantified extension class. Corollary 5.2 states it correctly. | Preserve quantifiers; source §1, points 5, 13, and 17. | Replace with the explicit sentence given below. This is a mathematical clarification, not a process remark. |
| §1, p. 2, lines 127–128, 132–133, and 146: “receives \(gf\),” “receives \(df\),” and “receives \(fe\).” | “Receives” does not specify the relevant factorization or fixing equation by itself. Its meaning is recoverable from context but is not defined as terminology. | Source §1, points 17 and 26; independent preference for the exact equality. | State respectively \(r(gf)=gf\), \((d\operatorname{ran}(f))(df)=df\), and \(\operatorname{ran}(fe')fe=fe\). |
| §3.1, p. 5, lines 375–377: “If \(t\) is closed, continuity gives …” | The defining inequality has been given, but the word “continuity” has not been assigned to it. | Source §1, points 11 and 17; definition-order convention. | Replace “continuity gives” with “the defining inequality gives.” |
| §1, p. 2, lines 94–95: “The constructions below are stated with the particular domain, range, and union hypotheses they require.” | This announces how the results are presented rather than identifying the hypotheses of a specific construction. It does convey a relevant distinction between the general framework and recursion categories. | Plugin economy requirement; source §1, point 12. | Optional: replace by the concrete dependency sentence below. Do not erase the distinction by silently making every result a recursion-category theorem. |
| §3, p. 5, line 324: “Some applications distinguish a subdomain in which conclusions are selected.” | “Some applications” is vague; the following definition gives the actual construction. | Independent editorial rationale; source §1, point 17. | Optional: “To select conclusions in a subdomain, fix \(s\le q\).” Continue with “Define the functor …” and remove the duplicated “Fix \(s\le q\).” |

The following exact replacements are recommended in priority order.

1. **Abstract.**

   ```latex
   In this arithmetic instance, every consistent computably enumerable
   extension of a consistent theory that strongly defines every recursive
   set numeralwise is incomplete; no enumerability assumption on the base
   theory is required.
   ```

2. **Range calculations.**

   ```latex
   To prove \eqref{eq:range-composition}, put
   $r=\ran(g\ran(f))$. Since $\ran(f)f=f$, we have $r(gf)=gf$.
   ```

   Preserve the following agreement argument. Replace the next occurrence by:

   ```latex
   For \eqref{eq:range-meet}, the domains $d$ and $\ran(f)$ commute, so
   $(d\ran(f))(df)=df$.
   ```

   Replace the monotonicity sentence by:

   ```latex
   If $e\le e'$, then $\ran(fe')fe=fe$, so
   \eqref{eq:least-range} gives $\ran(fe)\le\ran(fe')$.
   ```

3. **Closure-preserving inverse image.**

   ```latex
   If $t$ is closed, the defining inequality gives
   ```

4. **Optional concrete scope sentence.**

   ```latex
   Deductive closure uses ranges and stable unions of the generated
   chains; the incompleteness theorem also assumes the representation
   condition of Definition~\ref{def:representation}.
   ```

   This is a preview, not a definition or a claim that the representation condition follows from the recursion-category axioms. Whether the role of the recursion structure is sufficient for the intended program belongs to the mathematical review.

## Material that should remain

No paragraph was found whose sole function is to reassure the reader that an unstated error has been avoided. In particular, the following are substantive mathematical statements and should not be removed as “non-mathematical remarks”:

- The local inequality for partial maps and the restriction of the adjunction to total maps (§1, p. 2, lines 155–164).
- The distinction between the closure inequality and equality (§3.1, p. 5, lines 382–383). It distinguishes the proved compatibility from a stronger property.
- The counterexample to arbitrary increasing countable joins (§5, p. 7, lines 528–533). It identifies why uniformity of the arithmetic construction matters.
- The explanation that generalization is unrestricted for sentence axioms (§5.1, p. 8, lines 556–561).
- The verification of uniform c.e. stage generation (§5.1, p. 8, lines 569–578).
- The algorithm for jointly recursive numeral substitution (§5.2, pp. 8–9, lines 602–616).
- The absence of an enumerability assumption on the base theory in Corollary 5.2 (p. 9, lines 641–655).

Ordinary proof directions such as “To prove,” “For the third,” and “To verify uniformity” explain the argument to the mathematical reader. They are not drafting-process remarks. The word “exactly” is mathematically appropriate when identifying domains, defining rule-map domains, or asserting the fixed-point characterization. Deleting it mechanically would obscure the intended equivalence.

## Definition order and notation

| Item | Location and status |
| --- | --- |
| Composition and restriction operations | §1, p. 1, lines 52–77: declared before the domain and range arguments. |
| Domain posets | §1, p. 1, lines 79–87: \(\operatorname{Dom}(X)\), order, bounds, and \(E_q\) are defined before use. |
| Range | Definition 1.1, p. 2, lines 97–109: universal property and uniqueness precede \(\operatorname{ran}\)-calculations. |
| Direct-image functor | §1, p. 2, lines 139–148: source and target precede object and arrow assignments; identity and composition laws follow. |
| Contravariant domain functor | §2, p. 3, lines 231–244: \(E:\operatorname{Tot}(\mathscr R)^{op}\to\mathbf{BDLat}\) is declared before assignments. The restriction to total arrows is explicit. |
| Rules and closure | §3, pp. 4–5, lines 264–335: types and support precede the stages; closure precedes theories. |
| Theory and extension | Definition 3.2, p. 5, lines 337–340: the fixed-point condition and direction \(b\le t\) are explicit. |
| Presentation category and functors | §3.1, p. 5, lines 356–383: category precedes functors and natural inclusion. The isolated word “continuity” can be replaced as above. |
| Negativity, consistency, completeness, separation | §4, p. 6, lines 387–403: defined before representation and the theorems. |
| Representation | Definition 4.1, p. 6, lines 405–419: \(\sigma\) and \(f_g\) are typed before the equations. |
| Arithmetic syntax | §5.1, p. 8, lines 537–542: confined to the arithmetic realization; the abstract sections do not introduce an undefined notion of open formula. |
| Strong numeralwise definition | §5.2, p. 9, lines 618–626: defined before its use in the representation argument and Corollary 5.2. |

The early use of “recursion category,” “prodominical,” and “Turing morphism” is accompanied by citations and a description of the intended structure. This prose review does not treat the absence of a full tutorial definition as a defect for the intended specialist audience. It also does not certify that the stated structure matches every cited source convention.

## Paragraph-function pass

Every prose paragraph was assigned a mathematical function. The following compressed inventory records that pass outside the manuscript; ranges include associated displayed formulas and proof paragraphs.

| Source lines | Functions |
| --- | --- |
| 31–41 | Abstract: construction, results, and application. |
| 46–50 | Motivation for ranges and unions in deduction. |
| 52–77 | Ambient structure, notation, and operations. |
| 79–87 | Domain definitions and order. |
| 89–95 | Recursion-category context and scope of assumptions. |
| 97–110 | Range definition, attribution, uniqueness. |
| 112–136 | Range identities and their proofs. |
| 138–164 | Direct-image functor, inverse image, laws, local inequality, total adjunction. |
| 168–190 | Stable-union definition, convention, and least-upper-bound consequence. |
| 192–229 | Union-calculus assertions and proofs. |
| 231–244 | Lattice structure and contravariant functor. |
| 246–261 | Finite-power union lemma and proof. |
| 265–282 | Rule data, support, and direct images. |
| 284–294 | Rule closure and stages. |
| 296–322 | Deductive-closure theorem and proof. |
| 324–335 | Selection of conclusions and restricted closure. |
| 337–352 | Theories, extensions, reflector, adjunction. |
| 356–369 | Presentations, their morphisms, identity, composition. |
| 371–383 | Contravariant functors, restricted inverse images, natural inclusion, closure inequality. |
| 387–419 | Negative domains, logical conditions, separators, substitution data, representation. |
| 421–455 | Inseparability theorem and proof. |
| 457–470 | Essential-incompleteness theorem and proof. |
| 472–480 | Inheritance of representation and proof. |
| 484–501 | Numerical category, domains, and ranges. |
| 503–526 | Uniform c.e. stable-union proposition and proof. |
| 528–533 | Counterexample to arbitrary increasing joins. |
| 537–542 | Effective syntactic presentation. |
| 544–561 | Recursive rule maps and generalization convention. |
| 563–578 | Stages and uniformity proof. |
| 580–591 | Identification with derivability and examples. |
| 595–600 | Arithmetic negative domain and logical interpretation. |
| 602–616 | Formula enumeration and numeral-substitution algorithm. |
| 618–626 | Strong numeralwise definition and consequence of consistency. |
| 628–639 | Recursive complementary pairs and categorical representation. |
| 641–656 | Arithmetic essential-incompleteness corollary and transfer proof. |
| 658–668 | Bibliographic sources. |

The title, abstract, all headings, statements, proofs, unnumbered explanatory paragraphs, diagram context, bibliography, and source comments were included. There are no source comments, footnotes, appendices, or editorial acknowledgments in this version.

## Scope

This review read the complete LaTeX source and extracted text from all nine PDF pages. PDF page boundaries were checked against the extraction; the PDF was not rerendered or visually inspected in this review, and the source was not recompiled. No manuscript changes were made. The recommendations above preserve the mathematical statement of the body rather than certify its correctness, historical positioning, or fulfillment of the Di Paola–Heller program. Those questions are assigned to the separate hostile mathematical review. No claim of compliance depends on unread portions of *Mathematical Writing*.
