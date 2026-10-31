# Organization and abstract review

Paper: *Local connectedness in recursion categories and essential incompleteness*, version 9.
Source examined: [modular source at commit 3154b2f](https://github.com/flengyel/CategoricalEssentialIncompleteness/tree/3154b2f063c7101d2c678ee926a5a7bb661ba94b/manuscript/local_connectedness).
Review date: 31 October 2026.

The abstract does not adequately explain the paper's purpose. It presents the
inseparability theorem, much of its hypothesis list, and a counterexample before
stating an incompleteness conclusion. The categorical form of essential
incompleteness should organize the account. Inseparability and section lifting
are the means of obtaining that result.

The Di Paola–Heller program is absent from the abstract and appears in the
introduction only under Related work. This treats the paper's governing problem
as historical background. Di Paola and Heller identify the algebraization of
generalized incompleteness as a principal reason for their categorical recursion
theory in the opening of *Dominical categories: recursion theory without
elements*, pp. 594–595. See the [publisher's extract](https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/dominical-categories-recursion-theory-without-elements1-2/2E11506A81794B06EF34603881D79394).

## Current outline

The following is the existing order, not a proposed reorganization. The listed
functions describe what each part contributes to the argument.

| Part | Existing content and function |
|---|---|
| Abstract | Previews the lifting theorem, the Miller application, syntactic and arithmetic applications, and the cosheaf construction. It currently gives the lifting hypotheses and their limitations precedence over essential incompleteness. |
| 1. Introduction | Summarizes the lifting theorem and applications. **1.1 Related work** locates the work in categorical recursion theory, the Di Paola–Heller program, and the Miller literature. |
| 2. Categorical preliminaries | **2.1 Partial maps and restriction idempotents:** fixes restrictions, their order, inseparability, ranges, and restriction splitting. **2.2 Products, coproducts, and local connectedness:** supplies the structural definitions, the author's definition of range functor, and weak choice. **2.3 Recursion categories:** defines Turing morphisms and the recursion categories used in the paper. |
| 3. Sections of partial monomorphisms and inseparability | **3.1 Sections in a locally connected category:** constructs sections and proves the range-functor lifting theorem, **Theorem 3.3**. **3.2 A sufficient condition for lifting:** obtains lifts from joins of morphisms with disjoint domains, **Proposition 3.4**. **3.3 From inseparable restriction idempotents to incompleteness:** **Corollary 3.5** makes the theorem and refutation restriction idempotents inseparable in every represented consistent extension and excludes completeness. |
| 4. Miller sequences and essential incompleteness | Introduces Miller's sequence and its representations. **4.1 Computation independent of the binary representation:** constructs the recursion category and verifies the lifting hypothesis. **4.2 The index sets below and above 1/2:** proves inseparability by a recursive reduction and shows that each fixed representation computes a separator. **4.3 A theory of real closed fields:** constructs the theory and proves **Theorem 4.5**, essential incompleteness for consistent extensions whose axiom sets have the specified semidecidability. |
| 5. The syntactic recursion category | Defines the objects, numerical codings, provability quotient, and categorical operations of the syntactic category, using Montagna's arithmetization results. Compares the chosen presentation with Montagna's. Supplies the category interpreted in Sections 6–7 and the computation formulas used in Section 8. No subsections. |
| 6. Interpretation in models | **Proposition 6.1** constructs the interpretation in each model and proves preservation of the required structure. No subsections. |
| 7. A faithful family and theory extension | **Theorem 7.1** combines the model interpretations into a faithful range functor with locally connected target and gives compatibility with theory extension. **7.1 Lifting in the syntactic category:** supplies section lifts and obtains inseparable pairs in the syntactic categories, preserved under consistent theory extension (**Corollary 7.3**). |
| 8. Essential incompleteness of arithmetic | Applies the categorical criterion to numerical computation, proof conclusions, negation, and numeral substitution. **Corollary 8.1** gives recursively inseparable theorem and refutation sets for every consistent computably enumerable extension of PA. **8.1 Numeral instances and theory extension:** makes the associated pairs and extension maps explicit, relates numerical observations to the model interpretation, and compares the argument with Bernardi's. |
| 9. A recursion category from a three-point space | Constructs the category, citing Appendix A for its structural proofs. **9.1 Local connectedness and lifting:** verifies the criterion's hypotheses and distinguishes the category from the classical recursion category. **9.2 Evaluation functors:** constructs component functors and proves their preservation properties. **9.3 Propositional theories and component theorem sets:** constructs a consistent propositional theory; **Theorem 9.2** proves incompleteness of every represented consistent extension and recursive inseparability of the inverse images of the component theorem and refutation sets under the component atom maps. |
| A. The three-point cosheaf construction | **A.1 Cosheaves and functor categories:** compares cosheaves with fork diagrams and establishes the total category's structure. **A.2 Partial maps, ranges, and connected restriction idempotents:** proves the partial category's structure and local connectedness. **A.3 A universal object and a frame:** constructs embeddings and coding isomorphisms. **A.4 A Turing morphism:** proves **Theorem A.7**. **A.5 The recursion category and its splitting:** constructs the recursion category, identifies its splitting, and distinguishes it from the classical category. Supports Section 9. |
| B. Finite syntax and proofs | **B.1 The syntax algebra:** characterizes the formula object by initiality. **B.2 The proof object and its range:** proves theorem closure and consistency in the propositional construction. **B.3 The universal property of the proof object:** identifies an initial algebra in a slice category. **B.4 First-order derivations and sentence proofs:** characterizes derivations by initiality and sentence proofs by a pullback. B.1–B.3 support Section 9; B.4 also supports Sections 4 and 8. |
| C. Necessity of section lifting for inseparability | **Proposition C.1** supplies a counterexample when the lifting hypothesis is omitted. It explains an assumption in Theorem 3.3. No subsections. |

The principal results have the following relationship. Theorem 3.3 constructs
an inseparable pair. Corollary 3.5 transfers its inseparability to the theorem
and refutation restriction idempotents under the stated inverse-image
inclusions. It therefore excludes complete consistent extensions represented
by larger restriction idempotents. Theorems 4.5 and 9.2 verify this categorical
criterion for constructed theories; Corollary 8.1 recovers the arithmetic case.
Sections 5–7 provide a further application of the inseparability theorem to
syntactic categories and establish compatibility with theory extension.

## Comparison with Mathematical Writing

The governing source is Knuth, Larrabee, and Roberts,
[*Mathematical Writing*, Stanford report](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf).
The relevant verified advice is: motivate the reader and consider what the
reader needs next (§1, point 12, printed p. 3); make the opening paragraph and
first sentence especially effective (§1, point 24, p. 5); avoid unnecessary
jargon (§1, point 26, p. 5); and judge the placement of definitions in context
(§4, p. 9). Lamport's discussion in §31, pp. 69–70, distinguishes clarifying
the idea and structure from merely repairing sentences. The recommendations
below apply that advice to this manuscript; they are not purported rules about
abstracts quoted from the source.

| Manuscript anchor | Difficulty | Governing principle or editorial reason | Recommended action |
|---|---|---|---|
| Abstract, opening sentence | Announces an inseparability theorem without saying why it is proved. | §1(12), §1(24): motivation and the opening. | Lead with the categorical form of essential incompleteness and its relation to the Di Paola–Heller program. |
| Abstract, paragraph 1, sentences 2–3 | Lists splitness, weak choice, inverse-image preservation, four preservation properties, and section lifting before giving the incompleteness result. | §1(12), §1(26), and contextual placement of definitions: the reader needs the result's purpose before this hypothesis list. | Give one sentence identifying Turing morphisms, range functors, local connectedness, and section lifting as the method. Leave the full assumptions in the theorem. |
| Abstract, “Preservation of products is not required.” | Interrupts the account to deny an assumption that the abstract has given the reader no reason to expect. | Editorial application of the requirement to give each sentence a relevant function. | Delete from the abstract. Its role in the body can be assessed when that section is reviewed. |
| Abstract, counterexample sentence | Gives a limitation of the lifting theorem before the principal consequence has been stated. | §1(12): order information according to what the reader needs. | Omit from the abstract. Retain the mathematical counterexample in Appendix C. |
| Abstract, paragraph 2, explicit index sets and recursive reduction | Describes an intermediate pair and a proof step before reaching the theory of real closed fields. | The abstract's purpose is to state the contribution and its scope. This is an editorial judgment, not a claim that the pair is unimportant. | Lead the application sentence with the constructed theory and its essential incompleteness. Specify the class of extensions in that sentence. Leave the reduction in Section 4. |
| Abstract, paragraph 3, syntactic and arithmetic assertions | Places distinct categorical and arithmetical conclusions in a rapid sequence, with “Its numerical instance” as the connection. | §1(10), §1(17): connected exposition and unambiguous sentences. | Distinguish inseparability in the syntactic categories from the separate arithmetic incompleteness application. |
| Abstract, final sentence | Compresses a category construction, a non-equivalence result, a propositional theory, and its extension property into one sentence. | §1(17): readable sentences. | State the constructed theory and its essential-incompleteness property directly; state the ambient category in a separate sentence if needed. |
| Introduction, §1.1 | The governing problem appears after the technical summary. | §1(12), §1(24): motivation and openings. | In the later introduction review, bring the Di Paola–Heller objective to the opening. |
| Section 3 title and roadmap | Name the method but omit the categorical incompleteness criterion proved in §3.3. | Match the expository hierarchy to the results. | Consider the title “A categorical criterion for essential incompleteness” when Section 3 is reviewed. |
| Introduction, description of the appendices | Presents the syntax and proof appendix as part of the cosheaf construction alone. | Make dependencies accurate. | In the introduction review, identify B.4's use in the Miller and arithmetic applications as well. |

## Abstract: diagnosis and terminology

The first five sentences concern the lifting theorem and its scope. Essential
incompleteness first appears in the ninth sentence, in the Miller application.
The general categorical criterion of Corollary 3.5 is never stated as the
paper's organizing result. The abstract contains main results, but it gives
proof machinery and qualifications too much space and prominence.

The technical terms in the first paragraph are defined in Section 2 or given
precise content in Theorem 3.3. Their defect here is placement and proportion,
not an absence of definitions. The author's definition of range functor
includes the stated preservation properties; the abstract need not reproduce
that definition. No change to the definition is recommended.

The necessary distinctions can be expressed with the results themselves:

- The general criterion concerns consistent extensions represented by
  restriction idempotents, with the inverse-image inclusions in Corollary 3.5.
- The Miller application concerns axiom sets semidecidable uniformly from
  every binary representation of the sequence. This specifies the extension
  class in Theorem 4.5 and belongs with that conclusion.
- The cosheaf propositional theory is constructed in the restriction splitting
  of the recursion category. Its ambient category should be named accurately.
- Sections 5–7 establish inseparability in syntactic categories. Section 8
  separately proves incompleteness of the arithmetical theories. Those two
  assertions should remain distinct in the abstract.

The current abstract's reference to the non-equivalence of the cosheaf
recursion category with the classical one describes a substantive example.
It has a different function from the product-preservation disclaimer. Its
inclusion should be decided by its contribution to the account of the example,
not by a mechanical prohibition on negative sentences.

## Organization recommendation

Retain the present body order during this abstract review. The theorem and
corollary precede their applications; the Miller construction gives an early
substantial example; the three-point construction has its structural proofs
in an appendix. No dependency examined here requires moving a section.

Change the hierarchy of the abstract's account:

1. State the categorical essential-incompleteness result and its place in the
   Di Paola–Heller program.
2. Identify the method in one sentence: a Turing morphism, a range functor to
   a locally connected target, section lifting, and the passage to theorem
   and refutation domains.
3. State the Miller theory's essential-incompleteness result with its specified
   class of semidecidable extensions.
4. State the cosheaf propositional construction and the corresponding result
   for represented consistent extensions.
5. State the recovery of arithmetic essential incompleteness. Mention the
   syntactic-category application distinctly if space permits.

This is an outline for the abstract, not a proposal to reorder the body.

## Prioritized repairs

Replace the opening with the following two sentences as the starting point
for a new abstract:

> We prove a categorical form of essential incompleteness in the
> Di Paola–Heller program. We give conditions ensuring inseparability of the
> theorem and refutation domains of every consistent extension represented
> by a restriction idempotent.

Then write the application sentences before compressing the method into a
single sentence. Remove the product-preservation disclaimer, the counterexample
sentence, and the sentence narrating the recursive reduction from the abstract.
The resulting abstract should be checked against Corollary 3.5, Theorem 4.5,
Corollary 8.1, and Theorem 9.2, with Corollary 7.3 kept distinct from the
arithmetic conclusion.

## Scope

The abstract and introduction were read in full. All section and subsection
headings were extracted, and the principal statements and their dependencies
were checked across the body and appendices. The mathematical-writing plugin
was used; the relevant passages of its governing Stanford source were consulted
directly. This is an organization and abstract review, not a renewed
line-by-line review or proof audit of the entire paper. The review itself
recommends changes without implementing them. During the review, the
author requested the terminology “morphism.” That substitution was applied
throughout the current mathematical prose, with the necessary changes from
“an” to “a.” It is the only manuscript edit in this step; the proposed abstract
opening remains a recommendation. The assembled PDF was rebuilt and checked.
LaTeX diagram commands retain their required syntax.
