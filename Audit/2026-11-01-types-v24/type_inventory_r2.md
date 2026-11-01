# Second type check of §7.2

Reviewed file: `tmp/review24/round2/08a-uniform-theories.tex`, together with the revised declarations in §7.1 and the previously inspected dependencies. This check covers the entire revised section, including every newly introduced symbol and displayed composite.

## Resolved findings

| First-round finding | Second-round result |
| --- | --- |
| The codomain coding of the conclusion index was unspecified. | Resolved at lines 34–61 and 290–318. The predicate `D`, projection graphs `r_0,r_1`, and product isomorphism `v` are fixed; the represented arrow is explicitly `v⁻¹cu`. Thus the output pair in `Prov(e,z)` has the required coordinates. |
| The slice equivalence lacked complete actions. | Object action and pullback-morphism action are now given at lines 161–177; the quasi-inverse object and arrow operations are supplied at lines 178–182. A final endpoint declaration for the quasi-inverse arrow variables is requested below. |
| The natural comparison lacked components and a naturality equation. | Resolved at lines 209–241. Both component categories and endpoints are stated, and both sides of the naturality equation have the declared common source and target. |
| Algebra structures were suppressed. | The initial algebra is explicitly `((P^all,c^all),α)`; the transported structure is `Ξ_e(δ)ζ⁻¹`. The algebras `𝔓_e,𝔓_{≠e},𝔔` are distinguished from underlying slice objects. One pronoun ambiguity remains at the final identification, noted below. |
| The nullary map, terminal maps, and projections were implicit. | Resolved at lines 76–91, 125–129, and 150–203. The restricted rule data are typed for all arities. For `n=0`, `(k_{≠e}^Fm)^0=1_1` by Appendix A's power convention, and the unique premise map has codomain `1`; the construction includes this case correctly. |
| The search morphism had no stated representative. | Resolved at lines 344–358. The standard index has a declared typed index set, and both PA-provable graph assertions use the paired input code explicitly. The only branch interpretation subsequently used is the explicitly typed standard partial function at lines 381–399. |

## Remaining local declarations

1. **Slice object versus algebra, lines 278–281.** The sentence “Its underlying slice object is …, so it is isomorphic to the initial derivation algebra …” permits the second “it” to refer to the slice object. Repeat `𝔓_e` as the subject of the algebra-isomorphism assertion, and state that the isomorphism belongs to `Alg(H_e)`. The underlying slice object and an algebra are different types. The mathematical argument already proves the correctly typed assertion.

2. **Quasi-inverse morphisms, lines 178–180.** Under the user's strict requirement, specify the endpoints of the pair sent to `f+g`: `f:(X,x)→(X′,x′)` in `B/Fm` and `g:(Y,y)→(Y′,y′)` in `B/F_{≠e}`. The current phrase “a pair of slice morphisms” makes the types inferable, but does not state them.

3. **Algebra morphisms, lines 258–259.** Declare the algebra morphism's endpoints, for example `f:((Q,q),δ)→((Q′,q′),δ′)` in `Alg(H_E)`, before giving the pair `(f_e,f_{≠e})`. Its action and the transported structure already satisfy the correct algebra-morphism equation by the displayed naturality identity.

These are the only unresolved findings in this second type check. No erroneous composite, invalid nullary construction, missing existence hypothesis, or unjustified predicate identification was found. The canonical numerical presentation, pullback comparison, transported algebra structures, and final diagonal calculation check with the stated types. No additional appendix argument is needed.

The primitive-recursive symbols in arithmetic formulas are covered by the global convention in §5; no new language expansion is being silently assumed. The interpretation functors and the code functions are defined in the preceding sections. The audit does not require those definitions to be reproduced in full.

The strict explicit-type audit can pass after the three local declarations above are corrected and the resulting text is checked. No manuscript file was edited by this reviewer.
