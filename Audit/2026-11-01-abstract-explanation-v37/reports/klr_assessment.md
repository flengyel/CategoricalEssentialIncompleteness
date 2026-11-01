# Mathematical Writing assessment of the version 37 abstract

**Manuscript:** Florian Lengyel, *Logical consequence and essential incompleteness in recursion categories*, version 37, 1 November 2026, commit 47be761bc05fa0d176b2f9a48f5f63db63b9fa79.

**Diagnosis.** The abstract identifies the subject, historical objective, and substantive applications, but inserts body-level categorical machinery without briefly identifying the theories it constructs. “Generated theories” needs a short mathematical meaning: theories of sentences derivable from chosen axioms in the internal deductive systems. The abstract should state the contribution, main results, and their scope. It need not explain the entire construction or proof chain, and it should not become an introductory outline or roadmap.

The detailed connections between axioms, derivations, conclusion images, restriction ranges, the Turing morphism, comparison, and theory extension belong in the introduction and subsequent body. The isolated sentence about total morphisms and restriction splittings should not be repaired by adding a catalogue of definitions to the abstract.

## 1. Actual organization and contribution

The relevant source order is as follows. The separate main and appendix outlines give the complete subsection/result inventory. This outline supports the review and introduction planning; it is not material to reproduce as an abstract roadmap.

| Present unit | Function in the paper |
| --- | --- |
| §1, Introduction and related work | Previews comparisons and examples; places Di Paola and Heller's objective in the literature. |
| §2, Categorical preliminaries | Defines partiality, ranges, restriction splitting, range functors, and Turing morphisms. |
| §3, Diagonal comparison and complementary conditionals | Uses a Turing morphism and specified lifts to obtain a categorical obstruction to completeness and a source-inseparability criterion. |
| §4, Internal theories and semantic consistency | Identifies generated theories with theorem domains, introduces refutation by negation, and proves separate semantic-comparison and consistent-extension criteria. |
| §5, The syntactic recursion category | Realizes syntax, substitution, derivations, and generated theories in the total restriction splitting of the syntactic category. |
| §6, Interpretation and soundness | Interprets the internal syntax; proves standard-code soundness using a model of the represented axioms and transports it to arithmetic ultrapowers. |
| §7, Essential incompleteness of arithmetic | Applies the comparison to represented arithmetic theories in a fixed ambient category, obtains uniform independent sentences, and compares the numerical realization. |
| §8, Miller sequences | Constructs representation-independent computation, an inseparable cut pair, and an expanded real-closed-field theory with the specified uniform extension condition. |
| §9, Three-point cosheaves | Constructs the recursion category, internal propositional derivations and their theory, and two essentially incomplete endpoint theories. |
| Appendix A | Gives the categorical construction of syntax, inference, deductively closed images, sentence theories, and their representation by ranges. |
| Appendix B | Supplies the cosheaf/functor-category construction and its recursion-category properties. |
| Appendix C | Shows the conditional lifting requirement cannot be inferred from preservation and faithfulness alone. |
| Appendix D | Supplies the auxiliary faithful all-model interpretation and its limitations; it is not the main arithmetic soundness argument. |

The current abstract has the following order:

1. General construction and Di Paola–Heller objective (sentence 1).
2. Specific first-order and propositional realizations (sentences 2–3).
3. General ambient machinery, images, comparison hypotheses, and extension language (sentences 4–9).
4. Specific arithmetic, soundness/ultrapower, Miller, and cosheaf conclusions (sentences 10–14).

The abstract therefore returns from an instance inventory to general machinery and then lists the instances again through their results. Combining each instance with its result would remove repetition. This does not mean that an abstract must narrate the full general argument before naming an application; its task is to identify the work and its conclusions, not to reproduce the introduction.

## 2. Source consulted and the relevant guidance

The supplied KLR PDF and text were consulted directly. Printed pages are two less than the corresponding PDF pages in this copy. The following are paraphrases; the applications below are this review's judgments, not additional rules attributed to KLR.

| Verified source | Relevant advice |
| --- | --- |
| Knuth, §1, points 10–13, pp. 2–3 | Connect the exposition, explain definitions, motivate what follows, and preserve meaning when formulas are skimmed. |
| Knuth, §1, point 17, p. 3; points 24 and 26, p. 5 | Make sentences readable, give the opening particular care, and avoid unnecessary jargon and noun strings. |
| Knuth, §§4–5, pp. 9–13 | Definition placement is contextual; postponement can work, but too much withheld meaning obstructs reading. |
| Herbert Wilf, §27, p. 59 | Give readers an early, plain account of the work and make its results identifiable. |
| Leslie Lamport, §31, pp. 69–71 | Establish the idea and audience; improve the organization rather than repairing isolated sentences alone. |
| Paul Halmos, §42, pp. 106, 111–112 | Organize without distracting; alternative mathematical threads need connections, not merely linear placement. |

These passages discuss mathematical exposition and papers; they do not prescribe the contents of a research abstract. No dedicated research-abstract recipe, prescribed sentence count, or universal word limit was located in these discussions. They do not justify requiring the complete construction or proof progression inside the abstract. The content priorities below are editorial judgments for this paper, not a formula quoted from KLR. The source is Knuth, Larrabee, and Roberts, *Mathematical Writing*, available at https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf.

## 3. Concrete findings and placement

Sentence numbers refer to the complete sentences of the abstract on manuscript p. 1; the line anchors refer to the current abstract.tex.

| Anchor | Actual difficulty | Abstract-level action | Material for the introduction or body |
| --- | --- | --- | --- |
| Sentence 4, lines 9–10: “These constructions take place in the regular categories of total morphisms in the restriction splittings.” | An unexplained ambient-category classification interrupts the statement of the contribution. The reader is not told what is being split or why this detail matters here. | Remove this standalone sentence. The opening's qualification “completions of recursion categories” can retain the setting without teaching the completion construction. | Explain which recursion category is being completed, how restriction idempotents provide splitting objects, and why the total category supplies the setting for syntax and images. |
| Sentence 5, lines 11–12: “regular images of conclusion morphisms give the generated theories.” | The term “generated theories” has no short logical identification. The sentence names the machinery before saying what its output means. | Identify the output in a clause: the theory of sentences derivable from chosen axioms in the internal deductive system. Describing the image construction is optional here. | Explain the axiom subobject, initial derivation algebra, conclusion morphism, sentence pullback, and regular image, with their types. |
| Sentences 5–6, lines 11–14 | “The theorem and refutation domains” appear without an antecedent connecting them to the theories just constructed. | If these terms are retained, identify them as the provable and refutable sentences of those theories. No image-to-range derivation is needed in the abstract. | Explain how the same sentence subobject is represented by a restriction idempotent and how inverse image under negation gives refutation. |
| Sentences 6–8, lines 13–17 | The range functor, validity subobject, negation inverse image, total reduction, and partial conditional lift read as a list of proof data. | State the comparison theorem's result and retain only a short qualification needed to prevent an unrestricted claim. Its technical premise list can be omitted without claiming that an arbitrary functor preserves incompleteness. | Explain what is interpreted, what is reduced to what, how soundness yields the relevant disjointness, and how the specified conditional lift is used. |
| Sentence 9, lines 17–18: “consistent represented extensions” | “Represented” does not itself identify the effective extension class. | State the essential-incompleteness conclusion with the concrete extension classes in the application statements. The fixed-reduction mechanism need not be explained in the abstract. | Explain why enlarging the axiom subobject enlarges the generated theory and preserves the relevant inseparability reduction. Keep the semantic-comparison and source-inseparability arguments distinct. |
| Sentences 2–3 and 10–14 | The examples are first catalogued by category and logic and later catalogued by conclusion. | Combine each instance with its result where this improves economy. The abstract needs an intelligible summary, not two inventories separated by technical machinery. | Develop each construction's role and compare it with the general criterion in the introduction. |
| Whole abstract: no explicit Turing-morphism account | This absence is not, by itself, an abstract defect. | A brief method clause may mention a Turing morphism if useful, but no account of its role is required merely to satisfy a checklist. | The introduction should explain what the recursion-category structure contributes beyond the initial-algebra/image construction available in a more general regular category. |

These are applications of the verified KLR principles about intelligibility, purpose, organization, and unnecessary jargon. They are not an abstract-specific prescription found in the book. Familiar terms can be previewed; neither a larger dictionary nor a condensed proof is the needed repair.

## 4. What the theories actually are: material for the introduction

The following account is appropriate to the introduction and body. The abstract needs only its short conclusion identifying the constructed theories, not all of these connections. In
\[
\mathcal D=\operatorname{Tot}(\operatorname{Split}(\mathscr R)),
\]
an axiom subobject \(A\hookrightarrow S\), with \(S\hookrightarrow\Phi\) the sentence subobject of the formula object, determines the internal inference algebra. Its conclusion morphism \(c_A:P_A\to\Phi\) is restricted to derivations with sentence conclusions, giving \(c_{A,S}:P_{A,S}\to S\). The regular image
\[
P_{A,S}\twoheadrightarrow T_{A,S}\hookrightarrow S
\]
is the least sentence theory containing the axioms: it represents precisely the sentences obtainable from those axioms by the internal deductive system.

Where the image inclusion has the stated partial inverse, this same theory is represented by
\[
t_A=\operatorname{ran}(c_{A,S}):S\rightharpoonup S
\quad\text{in }\operatorname{Split}(\mathscr R).
\]
For sentence negation \(\nu:S\to S\), the domain \(\nu^*t_A\) represents refutability. Thus the image-to-range identification supplies the domains used by the recursion-theoretic comparison. These are not unrelated theories introduced after constructing a deductive system.

In the arithmetic application, the ambient syntactic category is fixed at \(S_{\mathrm{PA}}\), while the represented axiom subobject varies. Consequently the theory generated internally from chosen axioms must also be distinguished from the arithmetic theory used to define equality of ambient morphisms.

There are two proof routes. Theorem 4.2 uses sound interpreted theorem/refutation domains, the total reduction, and the specified partial conditional lift. Corollary 4.3 instead retains a fixed reduction from a source-inseparable pair through every larger consistent represented theory. The former is applied to each permitted arithmetic extension; the latter is applied in the numerical, Miller, and cosheaf accounts. The introduction should explain their relationship without merging their hypotheses. An abstract can state the resulting criteria and conclusions without reproducing both arguments.

## 5. Definition and notation audit

The disputed expressions are defined in the manuscript. They are not missing from the paper as a whole:

- Restriction splitting and total morphisms: §2.1; the exact category used for logical construction: §4.1.
- Syntax, inference rules, and initial derivation algebras: Appendix A.2–A.5; their syntactic realization: §5.2–§5.4.
- Generated sentence theory: Appendix A.5, Theorem A.6 and the paragraph following it; §4.1; Theorem 5.9.
- Theorem and refutation domains: §4.1, through the range and sentence-negation morphism.
- Soundness factorization and the validity-disjointness condition: Proposition 4.1; standard-code realization in Proposition 6.6 and ultrapower transport in Theorem 6.9.
- Total reduction and conditional lifting: Theorems 3.1 and 4.2. Their importance cannot be replaced by a claim about arbitrary range functors preserving incompleteness.

The abstract therefore needs a brief identification of its mathematical output, not a larger dictionary or a full sequence of constructions. The generated theory can be identified as the theory of sentences derivable from chosen axioms in the internal deductive system. Its precise sentence-subobject and restriction-domain representations belong in the introduction and body. The completion can remain named at the abstract's level of detail while its exact category is introduced at the place of use.

## 6. Abstract content and introduction content

### Abstract

The following are content priorities, not a prescribed sentence count or a roadmap.

1. **Contribution and objective.** Construct internal deductive systems for propositional and first-order logic in the realized recursion-category settings, and obtain essential-incompleteness results addressing Di Paola and Heller's objective.
2. **Short identification of the constructed theories.** Make clear that these are theories of sentences derivable from chosen axioms in those internal deductive systems. A clause can supply this meaning; the abstract need not derive the image/range representation.
3. **Main results and scope.** State the arithmetic, Miller, and cosheaf conclusions with their different extension classes. A short method or soundness statement may be included when it helps identify the contribution, but the full comparison hypotheses and proof mechanism need not appear.

The arithmetic statement must preserve the consistent computably enumerable PA-extension class. The Miller statement must preserve uniform axiom semidecision by one oracle program from every binary representation of the sequence. The cosheaf statement concerns two propositional theories and consistent computably enumerable extensions in the same language. Those qualifications bound the results; they do not require a tutorial about the constructions.

### Introduction

The introduction is the appropriate place to connect the mathematical parts:

- Explain how chosen axioms and the internal inference rules determine finite derivations and their conclusions.
- Identify the generated sentence theory with the image of the conclusion morphism, and explain its representation as a restriction range.
- Introduce refutation through negation and explain why these domains are the objects to which categorical recursion applies.
- Explain the Turing morphism's role, the range-functor comparison, and the soundness and lifting requirements.
- Distinguish that semantic route from the fixed-inseparable-pair criterion and explain persistence under consistent axiom extension.
- Describe the specific realizations and their effective extension classes in relation to these results.

This account should be connected mathematical exposition, not an isolated list of technical names or a sentence-by-sentence summary of every theorem.

## 7. Minimal meaning to retain

A short abstract-level identification is:

> the theories of sentences derivable from chosen axioms in these internal deductive systems

That phrase identifies the output. It is not a complete abstract draft, and it does not require the abstract to present the axiom–derivation–image–range–comparison argument. The typed explanation in Section 4 of this report and the fuller connection described above are for the introduction.

## Scope

Read directly: the current complete abstract; §§3–4; the generated-theory realization in §5.4; the fixed-category arithmetic setup and comparison; the relevant soundness and ultrapower statements; the Miller and propositional application constructions and extension arguments; the KLR sections cited above. The separate outline agents read the full main and appendix sources. This assessment does not independently certify every proof, bibliography entry, or originality claim. No manuscript file was changed, no new abstract was installed, and no recompilation was performed for this read-only assessment.
