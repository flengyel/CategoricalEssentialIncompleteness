# Cockett 1990: citation verification and duplicated arguments

The attached original verifies the remaining citation. The paper contains one avoidable repetition in the numerical realization; its generic categorical construction and its substantive realization proofs should remain.

## Citation verification

The source is J. R. B. Cockett, *List-arithmetic distributive categories: Locoi*, Journal of Pure and Applied Algebra 66(1) (1990), 1–29, DOI 10.1016/0022-4049(90)90121-W. The supplied file is the published 29-page article; PDF pages agree with printed pages.

On pp. 5–6, Cockett defines `rec(A,B)` by its universal property for an action `A×X→X` and a seed `B→X`. Proposition 2.1 identifies this with initiality for `B+A×−`. Lemma 2.2 and Definition 2.3 on p. 7 define parameterized recursion by preservation under the functor sending `X` to `X×P→P`. For `B=1`, this is the list initiality stable under parameters used in Appendix A. Product symmetry accounts for the opposite order of the parameter factor. Cockett composes in diagram order; the manuscript writes `gf=g∘f`.

The current citation is correct. An optional precise locator is “Lemma 2.2 and Definition 2.3, p. 7”. Proposition 6.7 on p. 28 is stronger: it constructs list arithmetic on arbitrary objects of a slice, rather than only preserving objects pulled back from the ambient category. The manuscript does not claim that these two statements are identical.

All 31 bibliography entries and all 65 citation uses now have the recorded source support. The earlier original-text access gap is closed. This statement concerns the particular attributions in the manuscript, not certification of every proof in every cited work.

Original PDF SHA-256: `498c616cde927654db68da87b0c838aced4e852a2199f3cb34e78fcf5ba146cc`.

## Comparison with Cockett's arguments

| Manuscript passage | Relevant Cockett passage | Relationship and consequence |
|---|---|---|
| Appendix A, parameterized list hypothesis and Definition A.1 | Proposition 2.1, pp. 5–6; Lemma 2.2 and Definition 2.3, p. 7 | The same established list structure, already attributed. This is a dependency, not an additional theorem claimed by the manuscript. |
| Proposition 5.6, syntactic list realization | Theorem 5.5, p. 17; Proposition 6.1, pp. 24–25 | The result is a concrete realization of known list initiality. Using Cockett's theorem instead would require verifying arithmetic structure, the nil/cons decomposition, and contraction of the tail in the relevant category and slices. The current proof directly proves totality, functionality and uniqueness in the theory's graph equality. Substituting a citation would relocate these obligations rather than eliminate them. |
| Proposition 5.5, bounded many-sorted term/formula syntax | Introduction, p. 2 | Cockett explicitly places the broader result about all internally specified free algebraic constructions beyond this paper's scope. No theorem in the attached paper directly supplies the manuscript's nonlinear syntax polynomial and its parameterized realization. |
| Theorem A.5 and the derivation initiality proofs | Proposition 5.3, pp. 16–17 | Cockett constructs the least subsemirecursive object inside an object satisfying a list domain equation. The manuscript takes the regular image of an initial derivation algebra to obtain the least rule-closed subobject. The objects, hypotheses and proofs differ. Cockett explicitly removes regularity from his setting on p. 3. |
| Admissibility, free variables and capture-avoiding substitution | General list recursion | List recursion supports these definitions but does not supply their constructor equations or the coded realization. The quantified branches and the distinction between raw names and bound-variable renaming remain necessary. |
| Numerical, Miller and cosheaf realizations | No matching realization theorem in this article | The manuscript must still prove, respectively, recursive totality on the carriers, independence of binary representations, and naturality of the component operations. A general list theorem does not establish those properties. |
| Appendix B's nonempty words and frame isomorphisms | List arithmetic | The frame uses nonempty words and particular natural isomorphisms for the three-point construction. It is not a second proof of the logical list-object theorem. |

## One recommended consolidation

In Proposition 7.8, the paragraph at `sections/08c-numerical-realization.tex:404–417` repeats the free-variable and quantified-substitution branch checks after identifying the algorithms as the same coded algorithms already verified in Proposition 5.7. Their carrier and constructor equations have already been proved in PA, so they hold in the standard natural numbers.

After the displayed types at lines 398–403, replace only the repeated branch verification by:

```latex
For these same codes, Proposition~\ref{prop:st-substitution-realization}
proves the carrier and constructor equations in $\PA$.
They therefore hold in $\N$. Uniqueness of the parameterized folds
identifies these numerical morphisms with the categorical ones.
In particular,
```

Retain the following admissibility pullback, the type of the induced substitution morphism, and the sentence carrier. Retain the preceding proofs of numerical syntax and list initiality: those quantify over arbitrary algebras in the numerical category and do not follow merely by interpreting the syntactic initial algebras in the standard model.

This is a proposed local edit, not an applied proof deletion.

## Repetition worth retaining

The last substitution induction in Proposition 5.7 resembles the identity and absent-variable induction in Appendix A. Its additional conclusion is PA-provability of the restricted graph equations, rather than equality modulo an arbitrary theory `T`. It can be deduced from the appendix by explicitly forming the same predicate presentations in `P_PA` and applying the categorical result in `B_PA`; merely citing the result in `B_T` would be insufficient. The existing short direct PA induction is clearer than introducing that extra presentation argument solely to save a few lines. Retain it.

The few lines checking the propositional inference endofunctor in the cosheaf application also specialize the appendix's general argument. They identify the actual functor and its action in the application. No consolidation is recommended there.

## Caution about replacing the list proof by a citation

Two independent readings of the original p. 18 identify a problem in the printed proof of Lemma 5.6. Its statement correctly uses the target action `g:A×X→X`. The proof display instead composes the source constructor `r₁:A×R→R` after `1_A×a:A×R→A×X`, which is ill typed. Replacing that occurrence by `g` repairs the type but does not justify the following cancellation: `g` is arbitrary and is not assumed monic. The source constructor's monicity does not permit canceling `g`.

This identifies a defect in that printed argument, not a counterexample to Lemma 5.6 or Theorem 5.5. It does not affect the verified citation to Definition 2.3. It supplies a further reason to retain the manuscript's direct uniqueness proof instead of importing this proof without checking it.

## Scope and disposition

Three independent checks covered the exact citation, the mathematical overlap with Cockett, and repetition across the manuscript's realizations. The original source and the relevant displayed formulas were inspected; no reliance was placed on OCR alone. The paper's proofs have not been cut or rewritten in this task. The citation ledgers are updated, and the detailed comparisons preserve the distinct proof obligations of the appendix and the applications. No new bibliography entry is needed.
