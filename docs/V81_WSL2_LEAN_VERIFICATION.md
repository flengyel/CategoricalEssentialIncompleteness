# WSL2 Lean verification of manuscript v81

The 31 targeted commands for [6775f0b3a5fb668f9390b21440f3f6c57bc65930](https://github.com/flengyel/CategoricalEssentialIncompleteness/commit/6775f0b3a5fb668f9390b21440f3f6c57bc65930) passed from a clean checkout. The twelve Cockett–Hofstra modules and the two retained checks for Theorem 4.7 and Corollary 8.10 each built and passed strict elaboration. The complete current transitive audit covered 35,074 declarations. Only `propext`, `Classical.choice` and `Quot.sound` occurred. The six parser tests and the manuscript-only check passed. The official full replay of this commit was pending at publication. [Targeted receipt](reviews/V81_WSL2_AUDITS/tested-6775f0b/targeted.json.gz) · [Correspondence](../FORMALIZATION_STATUS_V81.md)

The earlier full v81 replay at `830d03a5adcf144a003feb36f88bd06e0c5b0cf5` passed all 2,073 commands. The intervening commit `98f8d0d50a0cc08885d07ab4d71ec6f6a7adf885` passed 237 targeted commands. Its full replay was running when these results were published. [First completed full v81 report](V81_WSL2_LEAN_VERIFICATION_830d03a.md) · [Full receipt](V81_WSL2_LEAN_VERIFICATION_830d03a.json.gz) · [Intervening targeted receipt](reviews/V81_WSL2_AUDITS/tested-98f8d0d/targeted.json.gz)

## Mathematical scope

All 77 numbered results and the three numbered definitions have Lean counterparts. Both readers checked all 80 rows against the active manuscript. The 852 distinct declarations explicitly named there have individual axiom evidence. The older crosswalk has 844 names. Proposition 10.1 and Theorem B.7 account for the difference. The two fresh readings cover the abstract, every section, all five appendices, and the claims used inside proofs and examples. [Active correspondence](../FORMALIZATION_STATUS_V81.md#numbered-statements) · [Complete assertion inventory](reviews/V81_WSL2_ASSERTIONS/README.md) · [First reading](reviews/V81_WSL2_AUDITS/tested-6775f0b/first/report.md) · [Second reading](reviews/V81_WSL2_AUDITS/tested-6775f0b/second/report.md)

In §1, Cockett and Hofstra’s Theorem 4.9(i) now has a proof at arbitrary formal powers. Given a partial combinatory algebra, each computable morphism from a product with the algebra admits a total computable parameter for the given application. Part (ii) proves that every morphism between powers of a Turing object is computable. Splitting the idempotents on these powers that split in the ambient category yields an equivalence preserving restriction in both directions. The source spells out the scalar convention at input and output arity zero. An independent expansion also verifies that inclusion takes binary restriction products to restriction products for all ambient source objects. [Statement checks](../Lean/CategoricalEssentialIncompleteness/V46ComputableTuringCategoryChecks.lean) · [Original-source comparison and standalone kernel export](reviews/V81_WSL2_AUDITS/tested-6775f0b/cockett-hofstra/README.md)

The two readers found one mathematical error, one ambiguity and six historical claims without proofs at their original types. Neither found a gap in a numbered result. The first reader counts the invalid unrestricted Di Paola–Heller inference in both the error and proof-gap columns, recording seven broad proof gaps. The second counts the six missing positive proofs in the proof-gap column and the false implication in the error column. Their underlying findings agree. Both identified one citation page to correct. The consecutive clean whole-paper count is **0 of 2**. The mathematical evidence for the remaining claims and the requested proposed manuscript edits follow. [First verdict](reviews/V81_WSL2_AUDITS/tested-6775f0b/first/verdict.json) · [Second verdict](reviews/V81_WSL2_AUDITS/tested-6775f0b/second/summary.json)

The proof-export comparison compiled the twelve new modules both independently and with Lake. All nineteen named proof roots could be replayed in an empty Lean kernel environment. The configured Lake build emitted six spacing and eight line-length warnings. The strict Lean commands returned zero. The two builds produced the same exported mathematical proofs. [Export receipt](reviews/V81_WSL2_AUDITS/tested-6775f0b/cockett-hofstra/receipt.json) · [Configured Lake transcript](reviews/V81_WSL2_AUDITS/tested-6775f0b/cockett-hofstra/lake-build.log.gz)

## Remaining literature claims

Six conclusions cited in §1 still need proofs at their published types. None is used to prove a numbered result in v81. The correspondence identifies the proof that supplies each nearby step of the manuscript. [Original hypotheses and dependencies](reviews/V81_WSL2_ASSERTIONS/historical-comparisons.md#historical-constructions-outside-the-present-proofs)

| Passage | First missing construction or inference | Reach in the paper |
|---|---|---|
| §1, lines 124–127. Bauer–Hanson, Theorem 6.4 | In the parameterized realizability topos associated with the Miller sequence, identify the represented unit-interval assembly with the internal Dedekind interval. Use the uniform realizer for Miller indices to prove that the natural numbers object covers that interval and apply the passage from the interval to all Dedekind reals. | Section 9 needs the external Miller sequence. Its existence at the specified program index and for every common binary name has a checked proof. [Manuscript](../manuscript/latex/sections/01-introduction.tex#L124) · [Miller witness](../Lean/CategoricalEssentialIncompleteness/V46MillerFixedPointChecks.lean) |
| §1, lines 166–171. Heller, Theorem 9.2 | Given a uniformly generated isotypical B♯-subcategory of a locally connected iteration category, construct its Turing completion and derive the universal morphism from the generator and frame. | The three examples in the manuscript construct their own evaluators. [Manuscript](../manuscript/latex/sections/01-introduction.tex#L166) · [Heller](https://doi.org/10.2307/2274486) |
| Same paragraph. Lengyel, Theorem 21 | Construct that completion and its Turing morphism in a separated iteration category. The absolute case would also follow by applying the relative theorem to the identity functor. | This is the absolute existence theorem in the related work. [Lengyel, §4](https://doi.org/10.1016/S0168-0072(03)00060-5) |
| Same paragraph. Lengyel, corrected Theorem 26 | Given a faithful iteration functor to a separated iteration category, reflect the finite simulations with their domains and obtain composition and the universal morphism in the Turing completion. | Appendix D proves faithfulness of its particular family of functors directly. [Author’s corrections](https://github.com/flengyel/errata/blob/5555e4fa1da7b8e3a0836dd1fbf1ca385cacd03b/lengyel2004/lengyel2004_repairs_v10.tex#L619) |
| §1, lines 203–206. Joyal’s argument, van Dijk–Gietelink Oldenziel, Theorem 5.19 | Construct the internal arithmetic-universe object and its enumeration of coded predicates. Lift the diagonal predicate along the enumeration using projectivity of the terminal object of the initial universe. Evaluation at that code forces true and false to coincide under syntactic completeness. | Theorem 5.3 gives its slice comparison by a separate proof. [Manuscript](../manuscript/latex/sections/01-introduction.tex#L203) · [Theorem 5.19](https://arxiv.org/pdf/2004.10482#page=25) |
| Same paragraph. Theorem 5.20 | For the consistent initial arithmetic universe, identify the truth subobject of the diagonal sentence with the equalizer of the two internal truth values, then deduce that this equalizer differs from the bottom subobject of the terminal object. | Lemma 8.9 proves consistency for the signed PA theory by examining its derivations. [Theorem 5.20](https://arxiv.org/pdf/2004.10482#page=25) |

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
