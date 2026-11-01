# Mathematical Writing review of the expanded numerical realization

**Disposition: the structural and universal-property repairs are successful; a few local type and presentation corrections remain.** The candidate separates numerical realization from numerical incompleteness and supplies the formerly omitted comparison functors, algebra structures, fold equations, and computability arguments. The remaining findings arise chiefly from the newly explicit distinction between an object `C=(m,C_0)` and its carrier `|C|=C_0`.

Reviewed snapshot: version-26 candidate in `tmp/numerical26/round2/`, files `08c-numerical-realization.tex`, `08d-numerical-incompleteness.tex`, and the arithmetic assembly file. Line anchors below refer to the new files separately. I read both subsections in full, checked the imported definitions and fixed-code interfaces, and used the KLR source and governing conventions identified in the first report.

## Current outline and resolved findings

- **§7.4, The numerical realization:** define the two numerical categories and tuple codings; prove the total and partial category equivalences, regularity and coproduct properties, parameterized syntax/list initiality, substitution realization and derivation initiality; construct arithmetic sentence/proof objects and compare their concrete codes.
- **§7.5, Numerical incompleteness:** obtain the numerical inseparable pair through the lifting theorem and apply the domain-incompleteness corollary to the represented theorem and refutation domains.
- **§7.6:** the existing numeral-instance and theory-extension subsection follows.

These are appropriate separate purposes. The initiality proof now has the necessary typed data and equations: `Q,F,u,v` for the category comparison; `alpha`, `iota_P`, `h_T,h_F` for syntax; `beta` and `h_L` for lists; and `delta_A,beta,h_A` for derivations. The computation arguments correctly use programs that halt on their specified carrier inputs, with induction proving termination there. They do not impose total recursive extensions outside those carriers. The appendix remains used by reference for the general categorical constructions and the least-image theorem.

## Remaining necessary corrections

| Anchor in §7.4 | Finding | Required repair |
| --- | --- | --- |
| Lines137–145 | `Im(f)⊆D` and “enumerating C” use object names where the newly declared convention distinguishes objects from their underlying carriers. | Define `Im(f)` as an object with the dimension of `D` and carrier `|f|(|C|)`. Describe the enumeration as enumerating `|C|`; keep the factorization arrows as arrows between objects. |
| Lines242–245 | The function-operation example does not explicitly place `p,x_i` in their carriers, and says its value “belongs to X,” where `X` is an object. | State `p∈|P|`, `s∈|Σ_k|`, `x_i∈|X|`, `ξ(x_i)=p`; say its value belongs to `|X|` and lies over `p`. |
| Lines285–288 | The underlying cons operation is written with source `V×Z`, whereas its slice source is `(P×V)×_P Z`. The canonical identification is valid but unstated. | Precede the operation types by the canonical source isomorphism `(P×V)×_P Z≅V×Z` (with the parameter determined by `z:Z→P`). Then state `β_1:V×Z→Z` as the operation under this identification. |
| Lines345–353 | A stored derivation-tree label is numerical, but “its label belongs to its R_n” treats a categorical object as a set and suppresses the encoding when `R_n` has a multidimensional carrier. `P_A^all` is then introduced as a carrier and immediately used as an object. | Store a code in `widehat R_n`, decode it to the rule instance before using `p_n,q_n`, and define `P_A^all` as a unary object whose carrier is the c.e. set of valid numerical derivation codes. |
| Lines363–368 | “values in Q” and “a value in Q” again use the categorical object in carrier-membership statements. | Replace by `|Q|` in those element-level statements. The slice object `(Q,q)` and arrows involving it retain the object `Q`. |
| Lines404–419 | Literal equality of syntactic and numerical derivation-code carriers also depends on the chosen numerical presentations of rule labels and premise/conclusion maps, not only the common tree constructors. | Construct typed computable comparisons between the two presentations of each rule object, preserving its premise and conclusion maps. Apply them recursively to obtain a bijection of the proof-code carriers commuting with conclusion. State these comparisons before the tree induction; no preservation of initial algebras by interpretation is required. |

Two further small explicit-data corrections discussed with the parent should also be made: the proposition statement should bind its arity bound `d` and specify the unary recursive coefficient objects used in its proof; the formula for `F(f)` should state that it is the represented carrier function of an arrow `F(X,e)→F(Y,d)` in `C`, rather than leave only the external set-function type displayed.

For consistency with the opening convention, explicitly begin the section with `X,Y∈O` before quantifying `e∈I(X,Y)`. In §7.5, call `zeta` an isomorphism, since that is its required role in the lifting theorem. Both are short declarations, not additional proof obligations.

## Source principles and interpretation

The carrier/object repairs are required by the author's explicit-type criterion and the plugin's supplementary conventions. KLR §1 points11 and14 support introducing data and using notation consistently. The precise rule-code choice prevents a compressed comparison from carrying an unstated choice of presentation; KLR points10–11 and17 support making the inference reconstructible. The source does not demand a new presentation for elementary categorical background, and this report does not ask for duplicated appendix proofs.

No unmarked switch to a set-based replacement of the categorical construction is needed. The numerical category is expressly presented by external c.e. carriers and computable functions, and the functors to the splitting category are named. The corrections keep the memberships and categorical arrows at their declared levels within that presentation.

## Closure and scope

After these local repairs, the revised proof retains the intended content and has no other necessary organizational or prose correction identified by this reading. A final check must inspect the corrected source, the code-comparison construction, and the rendered pages. This is a scoped editorial/type review, not whole-paper certification, literature verification, or Lean elaboration. No manuscript file was edited by this reviewer.
