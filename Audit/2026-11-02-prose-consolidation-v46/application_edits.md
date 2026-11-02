# Version 46 application prose pass

Scope: the eight assigned application files in *Logical consequence and essential incompleteness in recursion categories*, Version 46. The six arithmetic/Miller files were read completely before editing and continuously after editing. The delegated three-point pass did the same for §9 and Appendix B; its detailed log is `tmp/revision46/threepoint_edits.md`.

Source: c20 `revise-mathematical-prose` and its terminology/source-review supplements; supplied `tmp/review_sources/klr.txt`, §1, §§4–5 and the discussion of reader expectations and formula placement in §7. KLR §1.5 supports self-contained statements, 10–13 connected explanatory prose, 16 retention of important displays, and 17 left-to-right readability. The inline default comes from the user's instruction, not from an invented KLR rule.

## Actual outline and paragraph functions

- Arithmetic comparison: realize the fixed sentence theory; define the diagonal pair; prove its numerical representation and the partial proof-search lift; apply logical comparison; derive essential incompleteness. The remaining paragraphs identify numerical theory-extension maps and compare Bernardi's method.
- Indexed theories: construct the axiom family and inference algebra; prove fiber initiality using the slice decomposition and naturality; realize uniform provability numerically.
- Uniform independent sentences: construct the parameterized partial lift, specialize the Turing morphism, and derive the two contradictions at a consistent parameter.
- Numerical realization: define the numerical and c.e.-carrier categories; construct total and partial-map equivalences with natural inverses; prove parameterized syntax, list, and derivation initiality; compare syntax and derivation codes; transport theories and substitutions.
- Numerical incompleteness: identify the diagonal pair, construct total source conditionals, establish inseparability, and apply the domain-incompleteness result to theory extension.
- Miller application: define representations and the fixed-point property; prove uniform unanimity computation and category structure; reduce the cut pair; distinguish representation-dependent separators; realize syntax/lists/derivations with one program across representations; prove incompleteness of the real-closed-field theory.
- Three-point application and Appendix B: definitions, structural constructions and equivalences; conditional naturality; evaluation functors and their failure to preserve all universality; formula/proof initiality; essential incompleteness. Appendix B retains the cosheaf/partial-map structure, nonempty-word frame, Turing construction, and categorical distinction. See the child log for its block-by-block classification.

Every reviewed prose paragraph serves one of these definition, construction, proof, application, comparison, or counterexample functions. No paragraph was moved into an editorial or limitations section.

## Implemented repairs

| Anchor | Repair and rationale |
| --- | --- |
| `lem:arithmetic-proof-search` proof | Removed the repeated informal search/priority description after the invocation of `lem:syntactic-functional-search`; the cited lemma's search was checked. Retained the interpreted-disjointness argument, exact partial graph/domain equations, output decoding, and explicit source/target of the lift. |
| Arithmetic theorem/corollary proofs | Removed dispensable “exactly”/“also” and the repeated announcement that the argument applies to every extension. Kept the explanation that the separator's source lift need not be internally total. |
| Indexed-family construction | Removed the announcement “We specify the numerical presentation of the axiom family”; the presentation immediately supplies that information. Kept all product comparisons, slice morphisms, naturality, algebra transport and fiber-initiality checks. |
| `prop:arithmetic-theory-realization` opening | Removed the immediate repetition of variable/signature hypotheses already fixed in its self-contained statement. Kept every numerical universal-property proof. |
| Numerical realization | Removed a sentence merely announcing that the displayed formula specifies the function; removed a repeated declaration of `S_rec=Split(Rec)` and one repeated “same codes” phrase. All domains, image laws, span comparisons, naturality and inverse checks remain. |
| Numerical and Miller incompleteness conclusions | Removed final prose merely restating the immediately proved inequality as incompleteness. |
| Miller definitions | Combined the Cantor-space naming sentence with its definition; removed the blanket “All code operations below are restricted to their indicated carriers” after the carrier conventions. Preserved every actual carrier/type restriction and representation-uniformity requirement. |
| Short unnumbered formulas throughout | Moved simple definitions, functor types, and scalar/set equalities inline. Important construction formulas, long paired/multi-line formulas, numbered equations and diagrams remain displayed. |
| §9 duplicate arguments | Replaced the repeated five-versus-two-subobjects proof with `prop:fork-distinction`; retained its complete proof in Appendix B. Replaced the repeated endpoint formula with `eq:fork-turing-endpoint`, retaining its parameter-map argument. Both citations were checked for the same objects, categories and encodings. |

All v45 construction-opening credits remain: Miller/Bauer–Hanson, Curry's cosheaf definition, and Cockett–Lack's partial-map construction. No citation, theorem label, or numbered equation was deleted.

## Definition/type audit and deferred candidates

- `C,C'` in the partial proof-search lemma require disjoint truth sets only in the interpreted model. This proof remains distinct from the total conditional built from provable complementarity; no consolidation between the two was made.
- Numerical syntax/list/derivation initiality remains. The Section 5 proof does not cover every computable algebra operation in `C_rec`, whose totality need not be provable in the theory.
- The Miller realization remains separate: each program must have the same domain and values across every binary representation. This uniformity is used in images, descent, inverse maps, folds and derivation evaluation.
- The three-point conditional retains computability and naturality of component inverses. A generic compatible-join construction does not establish those facts here.
- Appendix B's nonempty-word frame and its inverse checks remain; this object differs from the syntax list algebra.
- The numerical derivation-code convention that membership witnesses are absent was retained because it fixes the codes used in the explicit comparison, rather than merely denying an unrelated claim.
- No further exact duplicate proof was identified in this assigned scope. No organizational restructuring was needed.

Checks: all eight files have balanced LaTeX environments, display delimiters and dollar delimiters. All 136 `ref`/`eqref` occurrences resolve to labels in the current manuscript. The six arithmetic/Miller files and the delegated two three-point files received continuous post-edit reads. No process commentary was inserted. Integrated compilation and rendered-page verification are assigned to the root agent; neither is claimed by this log.
