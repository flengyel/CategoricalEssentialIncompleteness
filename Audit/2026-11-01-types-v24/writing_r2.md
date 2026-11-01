# Mathematical-writing review, round 2

The corrected section resolves the substantial type omissions identified in the first round. Three small local ambiguities remain before the requested explicit-type review can pass. None changes the mathematical argument.

Scope: the complete frozen §7.2 source in `tmp/review24/round2/08a-uniform-theories.tex`, together with the revised passages of §§6 and 7.1 in that directory. The governing source and editorial criteria are those documented in `writing_r1.md`; the KLR source was consulted in that round. This round checks the corrected text against the findings and reads the newly introduced categorical constructions in order.

## Remaining corrections

1. **Algebra versus underlying slice object.** In `08a-uniform-theories.tex`, lines 278–281, the sentence “Its underlying slice object is …, so it is isomorphic to the initial derivation algebra …” has an ambiguous antecedent for the final “it.” The latter isomorphism is an isomorphism of algebras, not an isomorphism between a slice object and an algebra. Write explicitly that `𝔓_e` is isomorphic in `Alg(H_e)` to the initial derivation algebra, and then identify its underlying slice object. This preserves the established distinction introduced earlier in the revised proof.

2. **Total numerical negation function.** In `08-essential-incompleteness-of-arithmetic.tex`, lines 80–85, `Neg:N→N` is declared as a total function, but “negation of formula codes” specifies its values only on formula codes. Choose a primitive-recursive extension to all numerical inputs, or give the underlying numerical constructor on all inputs. The shortest adequate wording is “choose a primitive-recursive extension `Neg:N→N` of negation on formula codes.” Only values at sentence codes are used subsequently.

3. **Scope of the negation morphism in the soundness theorem.** In `06-interpretation-in-models.tex`, `ν:S→S` is introduced locally in Proposition 6.6 by “If … is sentence negation.” Theorem 6.9 later uses `ν` without binding it in the common setup or in that theorem. Declare `ν:S→S` in `B_PA` in the fixed setup before Proposition 6.6, or in Theorem 6.9. This supplies the intended type and scope; it adds no mathematical assumption.

## Findings resolved

- The ambient total category and the realized syntax objects are explicit.
- The nullary premise map and the higher-arity projections have stated types and index ranges.
- The initial algebra has a named structure map in its slice category.
- The partial inverse of the consequence image, its equations, and its partial-map category are explicit.
- The numeral complement, the two pullback functors, and the action of `Xi_e` on objects and morphisms are given. Its quasi-inverse is specified.
- The restricted rule objects and their premise and conclusion maps are typed; their defining equations have matching endpoints, including arity zero.
- The natural isomorphism has named components with explicit slice categories; its naturality equation has a declared common source and target.
- The induced equivalence of algebra categories has an object action and a morphism action. Complete algebras use distinct symbols from their underlying carriers.
- The numerical presentation of `E×S` is fixed by a product isomorphism, and the conclusion graph is transported through explicit input and output presentation isomorphisms.
- The graph and domain assertions for the partial proof-search morphism use a chosen program index and quantified arithmetic formulas.
- The Turing equations have explicit types, and the inclusion of the total parameter map into the splitting is stated before composition with `θ`.
- The semantic substitution condition now uses codes in the image of the interpreted admissibility inclusion; assignments and assignment changes have explicit types.
- The ultrapower comparison component and naturality equation are explicitly typed.

## Exposition and dependency checks

The order of the section remains appropriate: family of axioms, family of derivations, numeral fibers, uniform provability predicate, and uniform independent sentence. The expanded type declarations explain the categorical constructions; they do not introduce new terminology. The words slice category, algebra morphism, quasi-inverse, natural isomorphism, product isomorphism, and restriction splitting have their usual meanings.

No repetition of Appendix A's construction proofs was introduced. The section invokes its inference endofunctor and regular-image theorem, then proves the additional decomposition and fiber statements needed here. The semantic substitution proof and the numerical realization proofs remain application arguments and are retained.

The three corrections above are the complete remaining findings of this pass. Status: **not yet passed**, pending those local corrections. After their exact replacements are read, no further broad review is indicated unless a new mathematical or typing problem appears. This is a scoped writing and explicit-type assessment, not a certification of the whole manuscript. No new PDF was compiled or visually inspected by this reviewer.
