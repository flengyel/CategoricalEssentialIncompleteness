# Primary-source dossier: the Di Paola–Heller program

This dossier supports the review of *Deduction and essential incompleteness in recursion categories*, source at commit `a9da9ee538edbf4a57e4469185f014aa88c5daf8`. It records primary-source evidence and separates that evidence from conclusions about the present note. It is not a verification of every theorem in either source.

## Sources and access

1. R. A. Di Paola and A. Heller, “Dominical categories: recursion theory without elements,” *Journal of Symbolic Logic* **52**(3) (1987), 594–635, DOI [10.2307/2274352](https://doi.org/10.2307/2274352).
   - The original user-supplied PDF was read through Library: [Paola-DominicalCategoriesRecursion-1987(1).pdf](https://chatgpt.com/library?file_id=libfile_fbdc67ace4488191897a24fc4266f75d&account_id=personal).
   - The PDF has a JSTOR cover page: printed page 594 is PDF page 2; printed page 625 is PDF page 33.
   - Reviewed: §1, pp. 594–596; §8 introduction, p. 621; Definition 8.14 and Theorem 8.15, pp. 625–626; Definition 8.17 and Theorem 8.18, pp. 626–627.
   - The [publisher extract](https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/dominical-categories-recursion-theory-without-elements1-2/2E11506A81794B06EF34603881D79394) independently verifies the opening program statement and the five target forms. It does not contain all of the original introduction or §8.
2. A. Heller, “An existence theorem for recursion categories,” *Journal of Symbolic Logic* **55**(3) (1990), 1252–1268, DOI [10.2307/2274486](https://doi.org/10.2307/2274486).
   - The original user-supplied PDF was read through Library: [Heller-ExistenceTheoremRecursion-1990(1).pdf](https://chatgpt.com/library?file_id=libfile_2a2ed7eb715c8191ac9553520cf68d73&account_id=personal).
   - Reviewed: Introduction, printed p. 1252, PDF p. 2.

These checks used the original PDFs' extracted text. The images were requested but their pixel content was not independently inspected. Exact symbolic transcriptions from the OCR should therefore be checked against the PDF before publication. The prose passages supporting the conclusions below are unambiguous.

## What the primary sources state

| Source anchor | Verified content | Consequence for the review |
|---|---|---|
| Di Paola–Heller, §1, p. 594 | The principal aim is an algebraic formulation of generalized incompleteness through categorical development of the recursion-theoretic concepts used in its proof. Domains are endomorphisms; the development is to avoid dependence on underlying sets and elements. | A categorical result should be assessed by its categorical data and proof, rather than by the presence of category-theoretic terminology. |
| Di Paola–Heller, §1, pp. 594–595, formulations (1)–(5) | The targets include essential undecidability from definability of recursive sets or functions; inseparability of theorem and refutation sets; creativity; and effective inseparability for Rosser theories. The authors present these as alternative forms of generalized incompleteness. | It is not justified to reject a theorem merely because it establishes the inseparability form rather than all five forms. Recursive inseparability and effective inseparability remain different claims. |
| Di Paola–Heller, §1, p. 595, following (5) | Each listed form yields incompleteness of every consistent recursively enumerable extension. The authors call for algebraic analogues of creative and effectively inseparable sets and announce a future construction of dominical, and sometimes recursion, categories from polyadic algebras. | There is a stated intended connection between algebraic formal systems and recursion categories. The announced polyadic route is evidence of that intended connection, not a proved claim that it is the only possible route. |
| Di Paola–Heller, §1, p. 596, final two paragraphs | The authors require generalized diagonalizations expressed in recursion theorems and algebraic analogues of creative and effectively inseparable sets. The recursion theory should be intrinsic to the algebraic treatment of formal systems, rather than externally imposed. | The strongest source-grounded challenge is whether the note supplies the connection between its deductive presentations, representation condition, and the intrinsic recursion theory. Diagonalization itself is not contrary to the program. |
| Di Paola–Heller, §8 introduction, p. 621 | The stated task is to identify assumptions under which satisfactory analogues occur in recursion categories, prove existence and principal properties, and identify exactly when element-like assumptions are needed. | A mere renaming of a set-theoretic assertion would be insufficient. An actual categorical conditional theorem may be meaningful, but its instances and comparison with the intended notions must be checked. |
| Di Paola–Heller, Definition 8.14 and Theorem 8.15, pp. 625–626 | Separation uses a complemented domain. The theorem constructs a recursively inseparable pair using a Turing morphism, coproduct domains, and the categorical diagonal. | The note's complementary-domain notion has a relevant antecedent. Its Theorem 4.2 should be compared with this construction rather than identified with it without a proof. |
| Di Paola–Heller, Definition 8.17 and Theorem 8.18, pp. 626–627 | Effective inseparability requires a total morphism that works uniformly on indices of disjoint domain extensions; the subsequent theorem constructs such a pair under additional hypotheses. | The note's existence of a representing morphism for each complementary pair does not, as stated, supply this uniform operation. The note does not claim effective inseparability. |
| Heller, Introduction, p. 1252 | The generalization is intended to admit examples substantially different from the numerical prototype. | A numerical realization verifies an important instance. It does not by itself establish that the additional logical and representation data exist in substantially different recursion categories. |

## Comparison with the current note

The note's §3 constructs deductive closure from rule morphisms, ranges, and specified stable unions. Those categorical operations have a mathematical role in the construction. Its §4 proves inseparability directly from the representation equations and derives incompleteness of consistent closed extensions. That proof uses restrictions, total inverse image, products, and complementary domains. The Turing morphism described in §1 is not invoked in the proof of Theorem 4.2 or Theorem 4.3.

The note supplies the logical presentation, the negative operation, and the substitution operation as additional data. Its only developed realization is the category of partial recursive maps, with formulas and deduction represented by numerical codes. No construction from a polyadic algebra or comparable algebraic formal system to a recursion category is given. No comparison with the Turing-morphism construction of Di Paola–Heller Theorem 8.15 is proved. These are confirmed absences, not counterexamples to the conditional theorems.

The distinction needed in the final assessment is therefore:

- **Narrow claim:** an abstract, element-free domain argument proving the recursive-inseparability form of generalized incompleteness, with the stated arithmetic realization. The sources do not justify rejecting this solely because it is conditional, uses a diagonal, assumes representation, or works under weaker hypotheses than a full recursion category.
- **Stronger claim:** realization of the program through an intrinsic connection between algebraic formal systems and the recursion-category constructions, including the machinery developed for categorical recursion. That connection has not been supplied by the present note. Claiming it as established would require additional constructions and comparison theorems.

There is no verified primary-source requirement here for Kelly enrichment, a monoidal category of recursion categories, or use of every axiom of a recursion category in each proof. Such requirements must not be invented for this review. Nor does the absence of a nonnumerical example alone prove that none exists.

## Remaining uncertainty

The historical program is not a formal list of necessary and sufficient acceptance criteria. The sources support the distinctions above; deciding whether a particular partial realization deserves the phrase “realizes the program” remains a claim that must be made precise. This dossier does not establish that the present approach cannot be extended to meet the stronger claim. It identifies the connection that has not yet been demonstrated.
