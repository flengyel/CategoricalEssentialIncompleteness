# Resolution of the explicit-type review

The reviewers independently read the revised mathematical text. The primary agent made the corrections and supplied frozen snapshots for the next pass. No review or process commentary was inserted into the manuscript.

| Confirmed omission | Final correction |
| --- | --- |
| Imported rule objects had an implicit ambient category; the initial algebra was represented only by its conclusion map. | The realization in `B=Tot(Split(S_PA))` is stated, all rule maps are typed, and the initial algebra includes its slice object and structure morphism. |
| Nullary premise, projections, terminal maps, partial inverse, and complement maps were implicit. | Each is named and typed. The restricted rule objects are explicit pullbacks, with typed premise/conclusion maps and defining equations. |
| The slice equivalence lacked its morphism action and a typed quasi-inverse. | `Xi_e` and `Psi_e` now have source/target categories, object actions, and morphism actions. Pullback uniqueness gives functoriality. |
| The natural comparison's components and naturality were suppressed. | The comparison `ζ` is named; both component types and its naturality equation are displayed. |
| Algebras were conflated with their carriers in the initiality proof. | The algebra functor `Λ_e` transports structures by `Xi_e(δ) ζ^{-1}`. Algebra objects and their underlying slice objects have distinct notation. Algebra morphisms and underlying slice morphisms are distinguished. The final isomorphism is explicitly in `Alg(H_e)`. |
| The output coordinates of the conclusion program were not fixed by presentation data. | A canonical paired predicate `D` and product isomorphism `v:J(D)→E×S` are fixed. For `u:J(P_0)→P`, the represented graph satisfies `J(γ_c)=v^{-1}cu`. Thus the pair `⟨e,z⟩` in the theorem predicate denotes the required coordinates. |
| The proof-search morphism was described as having a graph without specifying a representative. | A standard index `a_ℓ` is chosen; both its PA-provable graph implication and exact-domain equivalence are displayed before defining `ℓ=[a_ℓ]_PA`. |
| The semantic substitution condition placed decoded expressions in a carrier of numerical codes. | The interpreted admissibility inclusion is typed as an injection into the product of code sets, and its membership condition uses formula and term codes. Variables and assignment values are quantified in their respective sets. |
| Remaining implicit types in the soundness and arithmetic arguments. | The ultrapower comparison component and naturality equation, the diagonal map and restriction idempotents, numerical functions, interpreted conditional, and negation in the soundness theorem all have explicit types. Numerical negation is chosen as a total primitive-recursive extension. Proof codes are described as codes. |

The categorical syntax, substitution, inference functor, least-image theorem, and range/image correspondence remain cited from Appendix A. Their proofs are not repeated. The numeral-fiber argument establishes the new base-change assertion; the semantic substitution and realization arguments remain in their applications.

No theorem was strengthened, no new literature claim was made, and no mathematical result was removed. The final reviewers found no unresolved local type, mathematical, or terminology defect in the examined section and corrected passages. The introduction and abstract remain deferred.
