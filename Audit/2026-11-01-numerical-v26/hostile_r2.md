# (A) Kill-shots / hard blockers

No counterexample to the proposition's main conclusions is established. **Local acceptance remains withheld for the round-2 snapshot because the generic axiom-label replacement and several remaining object/carrier distinctions need correction.** The original omissions have largely been repaired: named comparison functors, naturality, parameterized algebra structures and fold equations, option-valued substitution, the sentence pullback, and the numerical application are now explicit.

Reviewed completely: `tmp/numerical26/round2/08c-numerical-realization.tex` and `08d-numerical-incompleteness.tex`, together with their containing arithmetic input file. The source-line anchors below refer separately to these frozen files. Section 7.4 is the realization; Section 7.5 is now its numerical incompleteness application, and numeral instances follow as §7.6. The prior round's page numbers do not locate the expanded text, so the exact section and source lines provide the anchors.

# (B) Major weaknesses

## H5. Replacing the chosen axiom object by its image changes the displayed inference endofunctor

**Anchor:** §7.4, `08c-numerical-realization.tex`, lines 334–344: “Fix an axiom subobject `i_A:A↪S` … Use that image as the carrier of axiom labels. The realized rule data … define `H_A`.”

**Claim as written:** the construction is an initial algebra for the inference endofunctor attached to the originally chosen axiom subobject.

**Failure mode:** inconsistent_use / missing comparison. **Evidence:** direct inspection of Appendix A's nullary rule object, `R_0=L+A`.

The image inclusion is isomorphic over S to the chosen monomorphism, but it need not have the same object or its same elements. If the axiom labels are replaced by elements of the image carrier, the resulting nullary rule object and hence the inference endofunctor are correspondingly changed. The current proof does not provide the natural comparison of these endofunctors or transport their algebra categories. Thus it cannot silently keep the original symbol `H_A` after replacing its coefficient object.

This is easily avoided: retain the original A as the coefficient and label its elements by the fixed tuple coding. Its carrier is c.e., and its conclusion morphism `i_A` is computable on that carrier, so the same finite-node membership/computation tests and evaluation proof work directly for the original rule data. In the subsequent arithmetic specialization, explicitly choose the axiom inclusion whose carrier is the sentence-code predicate from §7.1; there the literal standard-code comparison is available without changing the generic construction.

**Downstream impact:** the universal property must concern the H_A stated in the proposition, not a merely isomorphic functor with no specified comparison. **Severity:** major but local and repairable. No change of theorem or additional axiom is required.

## H6. The literal arithmetic code comparison needs the same numerical rule-label presentations

**Anchor:** §7.4, lines 382–420: “choose exactly … numerical syntax codes”; “Both constructions use the same tree constructors”; and the literal equalities `G_N P_T^syn=|Prf_T|` and equality of conclusion functions.

**Failure mode:** ambiguous / missing chosen identification. **Evidence:** the generic rule objects in C are finite products and tagged coproducts of carriers, whereas §5 presents its rule objects numerically before inserting their labels into tree codes.

Using the same syntax trees and outer derivation constructor does not by itself make the numerical labels of an arbitrary chosen presentation of each rule object equal. The proof should explicitly choose the same tag and tuple coding for the arithmetic rule labels as in the earlier construction. It may instead provide recursive comparison maps, but then the displayed equalities must be expressed through those maps. The shorter repair is to choose the earlier rule-label presentations, including the axiom inclusion, for this specialization.

The new numerical comparison argument has the right form once this choice is explicit. Ordinary induction then compares identical node membership and premise/conclusion conditions; it does not claim that the interpretation functor preserves arbitrary initial algebras.

**Downstream impact:** Lemma 7.1's interpreted inequalities can be read literally as the new numerical inequalities only after this coding interface is fixed. **Severity:** major comparison/exposition omission, locally repairable; the intended inequalities remain plausible.

# (C) Minor issues

## H7. Residual object/carrier notation is inconsistent with the subsection's own declared distinction

**Anchor:** §7.4, lines 77–87, 137–145, 242–245, 347, and 361–368.

The subsection declares an object `C=(m,C_0)` and its underlying carrier `|C|` at lines 21–28. Several later descriptions still use objects where numerical carriers are intended:

- `F(f)=γ_Y f γ_X^(-1):D_e→D_d` displays a function between sets; write `F(f):F(X,e)→F(Y,d)` for the C-arrow and `|F(f)|:D_e→D_d` for the displayed function.
- Define the image object with its dimension and carrier `|f|(|C|)⊆|D|`; do not leave `Im(f)⊆D` and “enumerating C” to switch between a category object and an enumerable set without the declared carrier notation.
- Replace “its value belongs to X” by “its value belongs to |X|”. At derivation nodes, distinguish the element of `|R_n|` from its encoded numerical label. Replace numerical values “in Q” by values in `|Q|`.

**Failure mode:** inconsistent_use / ambiguous typing. **Evidence:** the explicit object/carrier definition and these occurrences. **Severity:** minor local notation corrections, necessary for the user's explicit-type requirement. The mathematical operations exist as intended.

## H8. The example operation source must include the parameter and child carrier conditions

**Anchor:** §7.4, lines 242–245: the function operation is defined on tuples `(p,s,x_1,…,x_k)` with `s∈|Σ_k|` and `ξ(x_i)=p`, and “Its representing program halts on every such tuple.”

**Failure mode:** missing source conditions. **Evidence:** the nullary case exposes the omitted condition: for k=0, the displayed child equations impose no restriction on p.

State explicitly `p∈|P|`, `s∈|Σ_k|`, and `x_i∈|X|` with `ξ(x_i)=p`. The operation's representing program is guaranteed to halt on those source tuples. As a small test, take P empty and Σ_0 singleton. The nullary source in the slice is empty; an everywhere-diverging program represents its empty operation. Without the condition p∈|P|, the current tuple description incorrectly permits arbitrary numerical p and the halting sentence is unjustified. This is a local source-description error, not a counterexample to syntax initiality.

**Severity:** minor and readily repaired, but relevant to exactly the partial-domain issue under review.

## H9. Name the canonical comparison used for the list cons operation

**Anchor:** §7.4, lines 285–288: `β_1:V×Z→Z` is called an underlying operation of the L_P-algebra.

The literal source summand in the slice is `(P×V)×_P Z`, with its projection to P. It is canonically isomorphic to `V×Z`: the inverse reconstructs p as z(z). State that this isomorphism is being used when defining β_1. Its projection equation is then the displayed `zβ_1=zπ_Z`. The declaration does not require a new theorem or a long diagram, but it should not silently identify the two objects under the current explicit-type requirement.

**Failure mode:** omitted chosen identification. **Evidence:** the slice version of the list functor defined in Appendix A. **Severity:** minor exposition/type clarification.

# (D) Cross-section consistency failures

The round-1 findings have the following status:

| Finding | Round-2 repair and status |
| --- | --- |
| H1, categorical comparisons | Q and F now have object/arrow definitions; u and v have component types and naturality equations. The span comparison has an arrow formula, identities/composition/restriction checks, fullness, faithfulness, and essential surjectivity. Substantive construction repaired; the local carrier notation in H7 remains. |
| H2, initiality structures | The K_P algebra structures, fold types, projection equations, algebra equation, evaluation termination, and uniqueness are now given. Lists and derivations likewise have explicit structures and fold equations. The arbitrary operations are used only on their specified sources. The generic axiom substitution H5 and local source/list clarifications H8–H9 remain. |
| H3, numerical application | Separate numerical and syntactic objects are named, the sentence map is a pullback of the full map, and the final restriction inequalities have their ambient objects stated. The actual choice of arithmetic rule-label presentations needs H6. |
| H4, substitution | Term substitution, total option-valued formula substitution, the admissibility pullback, and induced formula substitution are typed. The numerical algorithms and their constructor equations are expressly imported and justified by direct induction. Closed. |

The proofs of regularity and monomorphism partial inverses are valid on the newly typed c.e. carriers. The preimage-search computation is dovetailed and terminates on the surjection's codomain. The syntax and list evaluation proofs use totality only on the carrier of the relevant algebra operation. The node-count inductions for syntax and derivations therefore supply computable folds without assuming total recursive extensions on all numerical inputs.

The numerical incompleteness subsection correctly distinguishes `a,b` in Rec from `I(a),I(b)` in the splitting; defines the target objects and maps through Q; types the reduction inequalities; and uses fullness to preserve inseparability on original objects. Its final application invokes the actual categorical corollary. The remaining code-interface choice is confined to H6.

The two revised subsections now have distinct purposes: the numerical realization establishes the categorical syntax and theory construction, while the next subsection applies the comparison theorem to obtain numerical incompleteness. No proof of Appendix A's general least-image theorem is duplicated.

# (E) Acceptance conditions, non-negotiable

1. Retain the original axiom coefficient in the generic H_A construction, or explicitly transport along its isomorphism to the image coefficient. The direct retention repair is sufficient.
2. Fix the arithmetic rule-label presentations to the earlier numerical tag and tuple codes before claiming literal equality of standard proof carriers and conclusion graphs.
3. Correct the residual object/carrier descriptions and display F's actual morphism type separately from its underlying function.
4. State the full parameter/child source conditions for arbitrary algebra operations, including k=0.
5. State the canonical slice-product comparison used for β_1's source.

Each condition has a specific source anchor above. A final review of the corrected text is needed; no new substantive theorem, bibliographic search, or weakening of the proposition is indicated.

# (F) Not checked / uncertainty log

Read completely: the two frozen revised subsections, including every displayed composition and universal-property argument. Rechecked against the imported definitions of the syntax and list functors, inference endofunctor, syntactic numerical coding, standard interpretation, and diagonal application. This round does not re-audit all unrelated results or bibliography entries. The final rebuilt PDF is being handled by the parent workflow; this report's anchors are the exact frozen source ranges.

No Lean formalization or kernel check is claimed. No counterexample to the proposition's existence or initiality conclusions was found. The empty-parameter test in H8 concerns only the local unqualified operation-source sentence.

**Strongest confirmed blocker:** H5 changes the coefficient of the inference endofunctor without a corresponding transport argument; retaining A directly repairs it.

**Strongest suspected unconfirmed blocker:** none beyond the explicit coding choice needed for H6; no false numerical comparison has been established after that choice is made.

**Most important thing not checked:** all earlier syntax and semantic developments were used through the inspected interfaces rather than re-proved in full.

**Dependence on unavailable material:** none for these findings.

**Final recommendation:** unknown for whole-paper publication; **local acceptance withheld pending H5–H9**. The earlier major omissions are substantially repaired, and these remaining corrections are concrete.
