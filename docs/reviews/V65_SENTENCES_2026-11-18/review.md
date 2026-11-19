# Sentence review of manuscript v65 and corrections in v66

The recurring ambiguity in v65 is the scope of a short phrase. In the introduction, “one oracle program” needs to be attached to a particular partial function. In §9.3, “its negation” occurs immediately after the *other* strict inequality. In Lemma 8.9, the phrase “primitive recursive constructions” covers both an operation on proof codes and the inductions that justify it. Version 66 resolves all 33 sentences marked **Clarify**. It also revises four adjoining or related sentences.

Of the 2,686 sentences, 2,600 received a **Keep** judgment, 33 **Clarify**, eight **Reword**, 29 **Merge or move**, and 16 **Delete**. A merge retains mathematical content. For example, conclusion preservation is essential to the computable bijection in the introduction, although it can be stated as a property of that bijection in the same sentence. A deletion drops a sentence whose contribution is already present or whose subject has no subsequent use. The 50 outstanding suggestions concern economy and presentation.

## Outline and sentence records

Each linked table follows the order of the printed paper. A row gives the v65 sentence, its precise source, its function in the local argument, its clarity and economy, and the action taken in v66. The v65 text column reproduces the sentence in TeX, including any attached display. The last two columns give the v66 source line and the exact replacement where a sentence was revised. A reason and a proposed repair accompany every editorial intervention. Several kept sentences have a note identifying the inference that depends on them. The source links point to the audited v65 commit.

| Part | Sentences | Function in the paper |
| --- | ---: | --- |
| [Abstract](Abstract.csv) | 10 | The signed theory, the slice equivalence and the three realizations. |
| [1](1.csv) | 78 | The two general constructions, their realizations, then their mathematical antecedents in §1.1. |
| [2](2.csv) | 70 | §2.1 defines partial maps and splitting. §2.2 gives the preservation and connectedness conventions. §2.3 distinguishes recursion categories and Turing categories. |
| [3](3.csv) | 48 | §3.1 diagonalizes against a lifted, reversed conditional. §3.2 derives the obstruction to separation. |
| [4](4.csv) | 208 | §§4.1–4.3 interpret theorem domains and transfer inseparability to extensions. §§4.4–4.5 construct generation and compare deduction. §4.6 gives the free signed theory and its converse. |
| [5](5.csv) | 111 | §5.1 constructs the Turing category over a theory. §5.2 compares slices under inclusion. §5.3 uses evaluation to transfer completeness and the Boolean extension problem. |
| [6](6.csv) | 396 | Arithmetic graph equality gives the syntactic category. §6.1 presents its total splitting, §§6.2–6.3 realize syntax and substitution, and §6.4 realizes finite derivations. |
| [7](7.csv) | 179 | Model interpretation supplies the conditionals and preservation in §§7.1–7.2. §7.3 proves soundness on standard codes. §7.4 transports the factorization to ultrapowers. |
| [8](8.csv) | 476 | §§8.1–8.3 compare arithmetic domains and construct one morphism for all indices. §§8.4–8.6 pass to numerical derivations and numeral instances. §8.7 constructs and interprets the free signed theory. |
| [9](9.csv) | 234 | §9.1 constructs the uniform evaluator. §9.2 reduces its diagonal to the two strict cuts. §9.3 builds the field theory and §9.4 its associated categories. |
| [10](10.csv) | 311 | The effective fork yields a recursion category. §§10.1–10.2 separate endpoint and central behavior. §§10.3–10.5 give propositional incompleteness, first-order conservativity and slice transfer. |
| [A](A.csv) | 202 | A.1 fixes Boolean and parameter conventions. A.2–A.3 construct named syntax and admissible substitution. A.4–A.6 construct least closed subobjects and the two calculi. |
| [B](B.csv) | 218 | B.1 proves the cosheaf equivalence. B.2 describes partial maps, B.3 constructs the frame, B.4 the Turing morphism, and B.5 the two splittings. |
| [C](C.csv) | 80 | A source morphism may have a target section that has no ordinary recursive lift. The explicit oracle domain isolates the failed inference. |
| [D](D.csv) | 65 | A family of countable models detects inequivalent program graphs. D.1 follows the pair under extension, D.2 tests it on numerals, and D.3 gives the true-arithmetic counterexample. |

## Decisions that affect the reading

| v65 location | Possible reading | Decision |
| --- | --- | --- |
| Abstract, S0004 | Parameter stability appears to qualify derivations as well as syntax. The reader cannot tell which axiom inputs require initiality. | In v66, parameter stability qualifies syntax and lists. Initiality is required for each axiom subobject under consideration. Slice deduction receives its own hypothesis. |
| Introduction, S0029, and §4.6, S0369 | The universal assertion about consistent extensions can hold vacuously. The pronoun “its” in §4.6 has no named theory. | Both summaries now name the consistent theory. The reduction in §4.6 is expressly total. |
| Introduction, S0050 and S0056 | A reader might identify the model of the axioms with the model interpreting program graphs, or require a common program for distinct numerical functions. | Name the two models. Fix the partial function before quantifying over its program and require the same domain and values for every name of the Miller sequence. |
| §5.3, S0514–S0515 and S0519 | The reduction to the fiber works for an arbitrary closed slice extension. A Boolean morphism and its two fibers have different types. | Keep the word “any” and the evaluation argument. In v66 the fibers of a total extension give the separator, and a complementary separator defines the total extension. |
| Lemma 8.9, S1553–S1560 | A negative leaf is a node, whereas the entries in the finite list are labels. The last paragraph also conflates computing a valuation with proving its invariant. | Name the label, the common list from the two derivations, the operations on codes, and the PA induction proving truth of the conclusion. |
| §9.3, S1786 | “Its negation” appears to refer to the axiom just written, which would have the theory prove the negation of its own axiom. | Write the refuted sentence explicitly, $\neg(c_n<1/2)$. |
| Proposition 10.8, S2100 | “Substitution” can refer either to first-order term substitution or to uniform instances in the propositional proof. | Specify the substitutions for the propositional metavariable and give the modus ponens step for the fourth image. |

The comparison with Došen and Petrić concerns what a sentence enables the reader to check. In *Bicartesian Coherence* the two projections with the same source and target explain the need to distinguish derivations. In *Equality of Proofs for Linear Equality* the authors give a functorial meaning to coherence and explain which variable occurrences a diagram edge joins. The analogous details worth keeping here include the two roles of a model in §7, the name-dependent separator at one half in §9 and the failure of whole-open evaluation to preserve products or monomorphisms in B.1. Knuth, Larrabee and Roberts’s advice on motivation and on reading the prose with the formulas skimmed also informed the judgments. [Bicartesian Coherence, Introduction](https://arxiv.org/pdf/math/0006052) · [Equality of Proofs for Linear Equality, Abstract and §1](https://arxiv.org/pdf/math/0601490) · [Mathematical Writing, §1](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf)

## Definitions and notation

Section 2 gives the order of composition before the first restriction identities. Section 4.4 passes from a morphism $a:A\to S$ to its regular image before applying generation. In Corollary 4.8 and Appendix A.1 the injections into $1+1$ are ordered false, true. The first source summand of a separator can nevertheless map to true. Appendix A.3 needs its equal-binder branch even for a failed recursive substitution in the body. These conventions are used in the proofs. The only definition-order move suggested by the audit is local to A.1, where the sentence declaring the arity bound $d$ could precede its first use. The section order already places the main equivalence ahead of the long realizations.

## Corrected wording and dispensable sentences

- **§4.6.** “A consistent sentence theory is essentially incomplete if a total morphism reduces an inseparable pair to its theorem and refutation subobjects (Corollary 4.3).” The first adjective supplies a condition in the definition of essential incompleteness.
- **Lemma 8.9.** “Extraction of the positive labels, membership in the resulting list, and Boolean evaluation of a formula are primitive recursive on the codes. In PA, induction on each coded derivation proves that its conclusion has value true for the common list $L$.” The following sentence identifies where disjointness of the diagonal predicates is used.
- **§9.3.** “For $n\in R_a$, the axiom $1/2<c_n$ and the ordered-field axioms prove $\neg(c_n<1/2)$.” This gives exactly the negative half of the reduction.
- **§5.1 and §5.3.** S0448, “This proves the slice Turing property”, follows the construction of the required total parameter. S0516, “This proves the essential-incompleteness equivalence”, follows the two directions of that equivalence. Either sentence can be deleted without changing the proof. The two identities for the graph retraction and the quantification over arbitrary slice extensions should stay.
- **§1.1 and Appendix B.1.** S0083 gives a historical observation about modal provability with no role in the ensuing argument. By contrast, the fork in S2342–S2343 gives a two-element pushout where the product would have four elements, then supplies a monomorphism whose whole-open component identifies those two elements. Each sentence answers a different mathematical question.

## Coverage and verification

The inventory follows the input order in the v65 source archive, from the abstract through Appendix D. Mathematical displays belong to the surrounding sentence, including diagram sentences and numbered equations. A display ending an assertion closes that sentence. A control space after an abbreviation counts as typesetting. The title, author, date, headings, theorem captions and 39 bibliography entries were inspected separately as identifying material. The bibliography contains publication records, and all 39 entries have citations in the text. The review did not reverify the external literature's theorem proofs.

The v66 archive was compiled independently of the working TeX directory. The two versions have the same 77 numbered result statements, three numbered definitions and 157 labels. Sixteen proof environments contain prose changes. The produced PDF has 88 pages and resolves all references and citations. Visual inspection covered pp. 1, 6, 13, 17, 50, 66, 70 and 84. The existing underfull line in the Pour-El bibliography entry remains. The [v66 correspondence table](../../../FORMALIZATION_STATUS_V66.md) records Lean verification and the date of the last full replay.
