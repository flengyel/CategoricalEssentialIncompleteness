# Abstract of version 62

The v61 abstract was mathematically accurate. It introduced three symbols in the opening sentence, reached the incompleteness criterion in the fourth, and first named the recursion category in the fifth. The [revised abstract](../../../manuscript/latex/abstract.tex) gives the construction, setting, consistency hypothesis and criterion in the first sentence. Its other two paragraphs state the slice theorem and the three applications.

## (A) Kill-shots / hard blockers

No mathematical objection was sustained against the revised abstract.

## (B) Major weaknesses

The v61 opening left the reader to discover what the construction proves. The first sentence of v62 gives both directions of the equivalence in Corollary 4.8. The following two sentences describe the axioms and the adjunction of Theorem 4.7.

## (C) Minor issues

The v61 abstract had fourteen sentences and 290 words. Version 62 has ten sentences and 249 words, counting space-delimited words. In §36 of *Mathematical Writing*, Mary-Claire van Leunen gives an exercise in summarizing an article or book in at most ten sentences (printed p. 87). We used that exercise to test concision. Section 1, point 24 (p. 5), gives particular weight to the opening sentence. In §27 (p. 59) Herb Wilf recommends telling the reader at the outset what the paper does. The revision uses established mathematical terms without introducing temporary symbols. The introduction supplies the historical attribution to Di Paola and Heller. [Knuth, Larrabee and Roberts, Stanford report](https://www-cs-faculty.stanford.edu/~knuth/papers/cs1193.pdf)

## (D) Cross-section consistency failures

| Passage on p. 1 | Check against the numbered results |
|---|---|
| Generated theory | The consistency condition in Corollary 4.8 applies to the generated theory. In Theorem 4.7 the right adjoint also has consistent theories as its domain. |
| Slice over the theorem subobject | Theorem 5.3 covers every consistent closed extension of the constant family. It assumes deduction in the slices and a chosen global logical theorem. |
| Arithmetic | In Theorem 8.6 the numerical interpretation of one total morphism gives independent sentences for consistent indexed extensions of Peano arithmetic. |
| Miller sequence | Theorem 9.7 uses constants with their strict rational bounds and a single program that semidecides the extension axioms from every binary representation. |
| Three-point space | Corollary 10.6 allows a consistent computably enumerable extension in the language of either endpoint theory. |

## (E) Acceptance conditions, non-negotiable

The abstract names the setting and states the principal result on first reading, retains its hypotheses, and contains no citation or cross-reference commands. The only TeX files changed from v61 are the abstract and the dated version information in the preamble.

## (F) Not checked / uncertainty log

The assessment concerns the abstract and the results it summarizes. No objection from the v61 comparison remains open for this text. The abstract makes no claim requiring a new priority search. The judgment on the abstract does not require a fresh Lean replay or a judgment on journal acceptance.
