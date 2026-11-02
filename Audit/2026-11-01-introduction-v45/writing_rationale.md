# Introduction proposal for version 45

The current introduction combines the introduction's problem-and-results function with definitions and proof preparation already supplied in Sections 2–4 and Appendix A. The proposed file `introduction_proposal.tex` retains the explanatory connection between deduction and computation while removing the duplicated construction. No manuscript or abstract was edited.

## Actual outline and function

| Current passage | Function | Treatment in the proposal |
| --- | --- | --- |
| Opening and Di Paola–Heller criterion | Problem, objective, contribution and methodological distinction | Retain the two paragraphs verbatim. |
| “The connection between deduction and recursion” | Defines the restriction splitting, total category and syntax hypotheses | Explain the connection in words; leave formal definitions and notation to §2.1 and Appendix A. |
| “Let Phi…” and “When m_A…” | Constructs the sentence image and defines restriction-range consistency/completeness equations | Retain the interpretation of the construction, not its diagram, partial-inverse hypothesis or equations; §4.1 and Appendix A already contain these. |
| “There are two…” and “The second argument…” | Proof schemas, lifting condition/counterexample and persistence argument | State the two criteria and their roles. The theorem and corollary citations preserve their scopes; proofs remain in §§3–4. |
| Syntactic/arithmetic paragraphs | Category presentation, syntax realization, code/model distinction, soundness and arithmetic results | Retain the named authors, category, comparison target, meaning of M, separate interpretation of decoded formulas and resulting incompleteness statements. Leave graph-quotient definition and universal-property details to §5. |
| Miller paragraph | Construction of category, cut-pair definitions and reduction, logical application | Retain the computational condition and logical result. Leave the displayed cut sets and reduction to §8. |
| Cosheaf paragraph | Construction, nonequivalence, component theories and extension result | Retain its mathematical distinction and conclusion. Leave subfunctor and endpoint mechanism to §9. |
| Related work history, origins, Bernardi, Cockett, Ramesh and Miller | Attribution and comparisons | Preserve the relevant antecedents and differences; remove the repeated F-hat extension, arithmetic model-family product and repeated presentation of our construction. The product family is in Appendix D. |
| Roadmap | Locate arguments | Retain after the literature discussion, so it ends the introduction. |

## Source-grounded editorial rationale

KLR §1 points 10–13 require connected prose, explanations suited to the reader's progress, and prose that can be followed while formulas are skimmed. Point 24 concerns a purposeful opening; the existing opening is retained. Point 26 cautions against strings of nouns and unnecessary jargon. These principles support explaining why internal deduction connects to recursion without presenting the full factorization and completion setup twice. Lamport's discussion in §31, printed p. 70, distinguishes repairing sentences from attending to the structure of the discourse. No universal introduction template or mandatory length is attributed to KLR.

The proposal is approximately 1,000 whitespace-delimited words, compared with approximately 1,795 in the current source. The point is the change of function, not that numerical target. Every removed formal construction has an existing body location; no proof dependency is being cut from the paper.

## Definition order and qualifications

The proposal defines the two endpoints of F when it introduces the functor. Peano arithmetic and its abbreviation precede S_PA. M is explicitly the standard model on N or an ultrapower before F_M is introduced; Pfn is named as sets and partial functions at that introduction. The abbreviation c.e. is expanded at first use. The sequence a is typed before the Miller application. Split, Tot, Phi, S, axiom and derivation variables, L_a/R_a, F-hat and the model-family indexing notation are unnecessary in the introductory overview and are not used there.

The generic incompleteness statement refers to the theorem's hypotheses rather than asserting that soundness alone implies incompleteness. The arithmetic paragraph keeps the distinction between the structure interpreting program graphs and the model interpreting the decoded formulas. The Miller axiom condition still requires one program to work for every binary representation. The cosheaf result still concerns consistent c.e. extensions in the same language. Ramesh is described as deriving Löb. The no-postulated-Löb/Hilbert–Bernays statement occurs in the general-method paragraph, not as a contrast attached to Ramesh. Cockett's object remains restriction terminal.

## Attribution at construction sections

The introduction's citations do not replace attribution where the construction begins. The separate placement audit should implement early citations in the syntactic-category and Miller sections and preserve already adequate opening attributions in the cosheaf and Appendix A subsections. Attribution must name the borrowed input; our internal deductive systems and new applications must not be ascribed to a preceding author merely to obtain an opening citation.

Scope: the current introduction, the governing KLR passages, §4's interpretation/comparison criteria, and the arithmetic, Miller and cosheaf theorem statements were read for this proposal. The supplied literature comparisons were retained without a new priority investigation. This draft has not been compiled or rendered. It is a proposal for integration, not a fresh whole-paper correctness audit.
