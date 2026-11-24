# WSL2 Lean verification of manuscript v81

The current proof commit is [98f8d0d50a0cc08885d07ab4d71ec6f6a7adf885](https://github.com/flengyel/CategoricalEssentialIncompleteness/commit/98f8d0d50a0cc08885d07ab4d71ec6f6a7adf885). All **237 targeted commands passed** in a clean checkout. They include builds and strict elaboration of 117 affected or supporting modules, the complete current transitive axiom audit, the six parser tests and the manuscript-only check. The audit identified 34,773 named declarations and only the three permitted axioms. The official full replay at this commit was still running when Florian requested this publication. [Targeted command and axiom receipt](reviews/V81_WSL2_AUDITS/tested-98f8d0d/targeted.json.gz) · [Active v81 correspondence](../FORMALIZATION_STATUS_V81.md)

The earlier v81 proof commit `830d03a5adcf144a003feb36f88bd06e0c5b0cf5` passed the full pinned replay. All 2,073 official subprocesses returned zero. Both independent receipt checkers compared the original transcript, tested Git objects and the published gzip. [Completed full v81 report](V81_WSL2_LEAN_VERIFICATION_830d03a.md) · [Full v81 machine-readable receipt](V81_WSL2_LEAN_VERIFICATION_830d03a.json.gz)

The current commit adds the categorical Di Paola–Heller theorem with a nonzero identity, Bernardi’s two categorical theorems, Montagna’s productive morphism in the unprimed PA category and four results on finitary generation and factorization in Appendix A. The two independent readers agree on all 852 declarations in the 80 active correspondence entries for the 77 numbered results and three definitions. They identify one false unrestricted historical implication, one ambiguity and eight positive §1 literature claims whose proofs at the original types are still open. None is needed for a numbered proof. [Eight new comparisons](../FORMALIZATION_STATUS_V81.md#categorical-domains-and-factorization) · [First reading](reviews/V81_WSL2_AUDITS/tested-98f8d0d/first/source-verdict.md) · [Second reading](reviews/V81_WSL2_AUDITS/tested-98f8d0d/second/report.md)

## Remaining literature claims

Eight conclusions cited in §1 still need proofs at their published types. None is used to prove a numbered result in v81. The correspondence identifies the proof that supplies each nearby step of the manuscript. [Original hypotheses and dependencies](reviews/V81_WSL2_ASSERTIONS/historical-comparisons.md#historical-constructions-outside-the-present-proofs)

| Passage | First missing construction or inference | Reach in the paper |
|---|---|---|
| §1, lines 124–127. Bauer–Hanson, Theorem 6.4 | In the parameterized realizability topos associated with the Miller sequence, construct the internal Dedekind reals and the epimorphism onto them from the natural numbers object. | Section 9 needs the external Miller sequence. Its existence at the specified program index and for every common binary name has a checked proof. [Manuscript](../manuscript/latex/sections/01-introduction.tex#L124) · [Miller witness](../Lean/CategoricalEssentialIncompleteness/V46MillerFixedPointChecks.lean) |
| §1, lines 166–171. Heller, Theorem 9.2 | Given a uniformly generated isotypical B♯-subcategory of a locally connected iteration category, construct its Turing completion and derive the universal morphism from the generator and frame. | The three examples in the manuscript construct their own evaluators. [Manuscript](../manuscript/latex/sections/01-introduction.tex#L166) · [Heller](https://doi.org/10.2307/2274486) |
| Same paragraph. Lengyel, Theorem 21 | Construct that completion and its Turing morphism in a separated iteration category. The absolute case would also follow by applying the relative theorem to the identity functor. | This is the absolute existence theorem in the related work. [Lengyel, §4](https://doi.org/10.1016/S0168-0072(03)00060-5) |
| Same paragraph. Lengyel, corrected Theorem 26 | Given a faithful iteration functor to a separated iteration category, reflect the finite simulations with their domains and obtain composition and the universal morphism in the Turing completion. | Appendix D proves faithfulness of its particular family of functors directly. [Author’s corrections](https://github.com/flengyel/errata/blob/5555e4fa1da7b8e3a0836dd1fbf1ca385cacd03b/lengyel2004/lengyel2004_repairs_v10.tex#L619) |
| §1, lines 203–206. Joyal’s argument, van Dijk–Gietelink Oldenziel, Theorem 5.19 | Construct the internal arithmetic universe of the published argument and derive its triviality from syntactic completeness. | Theorem 5.3 gives its slice comparison by a separate proof. [Manuscript](../manuscript/latex/sections/01-introduction.tex#L203) · [Theorem 5.19](https://arxiv.org/pdf/2004.10482#page=25) |
| Same paragraph. Theorem 5.20 | For the consistent initial arithmetic universe, construct the subobject of its terminal object expressing internal truth equal to falsehood and prove that this subobject differs from bottom. | Lemma 8.9 proves consistency for the signed PA theory by examining its derivations. [Theorem 5.20](https://arxiv.org/pdf/2004.10482#page=25) |
| §1, lines 208–210. Cockett–Hofstra, Theorem 4.9(i) | Starting with an internal partial combinatory algebra, form its category of computable morphisms between finite powers and construct total parameters satisfying the Turing equations. | Section 2 proves recognition from evaluators and retractions. [Manuscript](../manuscript/latex/sections/01-introduction.tex#L208) · [Recognition theorem](../Lean/CategoricalEssentialIncompleteness/V46TuringObjectRecognition.lean) |
| Same paragraph. Theorem 4.9(ii) | From a Turing object, derive its internal partial combinatory algebra, choose the required class of idempotents in its category of computable morphisms and exhibit the equivalence after splitting them. | The manuscript proves the splitting and the equivalence it needs for its explicit examples. [Cockett–Hofstra](https://doi.org/10.1016/j.apal.2008.04.005) |

## Manuscript edits for the Web GPT

These suggestions apply to the next manuscript revision. Each linked passage is from the tested v81 edition.

**1. State the nonzero-identity hypothesis in §1.** Replace the sentence beginning “Di Paola and Heller proved” at lines 173–175, ending immediately before “Bernardi obtained.” The diagonal argument on journal p. 626 ends with the equation \(1_X=0\). In the one-object, one-morphism category the two diagonal domains admit a complementary separator. The tested proof now derives their inseparability from \(1_X\ne0\) using the stated sum-valued Turing morphism. Corollary 3.3 already includes this condition. [TeX passage](../manuscript/latex/sections/01-introduction.tex#L173) · [Corrected implication](../Lean/CategoricalEssentialIncompleteness/V46DominicalLiteratureChecks.lean#L24) · [Counterexample](../Lean/CategoricalEssentialIncompleteness/V46TrivialDominicalCategoryChecks.lean) · [Di Paola and Heller, Theorem 8.15](https://doi.org/10.2307/2274352).

~~~latex
Under their section and coproduct hypotheses, Di Paola and Heller obtain
recursive inseparability of the two diagonal summand domains of a Turing
morphism $\tau:X\times X\rightharpoonup X+X$ when $1_X\ne 0$
\cite[Theorem~8.15]{DPH}.
~~~

**2. Define effective extensibility in §8.3.** Replace the opening paragraph at lines 4–9. Consistency alone allows a complete theory, which has no independent sentence even when the additional axiom set is empty. Theorem 8.6 constructs the required single morphism for PA and treats every consistent extension in its stated family. [TeX passage](../manuscript/latex/sections/08b-uniform-independent-sentences.tex#L4) · [Checked complete-theory counterexample](../Lean/CategoricalEssentialIncompleteness/V46EffectiveExtensibilityChecks.lean) · [PA construction](../Lean/CategoricalEssentialIncompleteness/V46ArithmeticUniformIndependent.lean#L204).

~~~latex
Pour-El studies effective extensibility for a fixed presentation of a
consistent theory \cite{PourEl}. Such a presentation is effectively
extensible if there is a recursive function that, given an index for a
c.e.\ set of additional axioms, returns a sentence independent of the
extended theory whenever that theory is consistent. For PA we construct
this assignment in $\mathcal B$ using the Turing morphism of $S_{\PA}$.
~~~

**3. Correct the page number immediately before Corollary 8.4.** Item (3) in Di Paola and Heller appears at the top of printed page 595. On line 241 replace the citation with the following LaTeX. The theorem about definability of recursive sets and inseparability of the theorem and refutation sets keeps the same hypotheses. [TeX passage](../manuscript/latex/sections/08-essential-incompleteness-of-arithmetic.tex#L239) · [Checked arithmetic implication](../Lean/CategoricalEssentialIncompleteness/ArithmeticInseparability.lean#L84) · [Journal article, p. 595](https://doi.org/10.2307/2274352).

~~~latex
\cite[p.~595, (3)]{DPH}
~~~

**4. Explain the object of predicate symbols in categorical terms.** Florian asked that the Web GPT justify the level of detail in the abstract. The following is a short editorial option for the passage beginning “In the total category of this completion” and ending “the negations of the atoms on \(b\).” It retains the ensuing definition of essential incompleteness. [Abstract](../manuscript/latex/abstract.tex#L5) · [README explanation](../README.md#the-construction).

~~~latex
In the total category of this completion, take $X$ as the object of
predicate symbols. These are the only nonlogical symbols and take no
arguments. Write $S_X$ for the object of sentences. The atomic sentence
morphism $\theta_X:X\to S_X$ sends each $x:W\to X$ to the sentence
$\theta_X x:W\to S_X$ over $W$. Let $i_a:A\hookrightarrow X$ and
$i_b:B\hookrightarrow X$ be the inclusions of the two domains, and let
$\nu_X:S_X\to S_X$ be negation. The axiom subobject is the join of the
images of $\theta_X i_a$ and $\nu_X\theta_X i_b$. Let $T$ be its
deductive closure.
~~~

The quantifier over \(W\) matters because the construction is internal. Section 4 spells out restriction along each \(h:W'\to W\) by \(\theta_X\circ(x\circ h)=(\theta_X\circ x)\circ h\). For the inclusions \(i_a:A\hookrightarrow X\) and \(i_b:B\hookrightarrow X\), §1 and the definition before Theorem 4.7 give the axiom subobject \(\operatorname{im}(\theta_X i_a)\vee\operatorname{im}(\nu_X\theta_X i_b)\), where \(\nu_X\) is sentence negation. Theorem 4.4 gives the reason for the last sentence. For every closed theory \(U\), the generated theory lies in \(U\) exactly when the axiom subobject lies in \(U\). These equations provide the justification in the body of the paper. [Introduction](../manuscript/latex/sections/01-introduction.tex#L30) · [Parameterized atoms and axiom images](../manuscript/latex/sections/03b-internal-adjunctions.tex#L340) · [Least closed theory](../manuscript/latex/sections/03b-internal-adjunctions.tex#L16) · [Reviewed module comment](../Lean/CEIPalomar/Challenge.lean#L16).
