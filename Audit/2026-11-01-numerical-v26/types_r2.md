# Numerical realization: second type and dependency review

**Disposition: two corrections remain.** The new category, initiality, and numerical-application arguments address the principal round-1 omissions. Several carrier/object expressions still need correction, and the asserted literal equality of the two full proof-code carriers requires a stronger coding identification than the text gives.

Reviewed frozen files: `tmp/numerical26/round2/08c-numerical-realization.tex`, `08d-numerical-incompleteness.tex`, and the containing arithmetic file. Line anchors below refer to the two new subsection files. No manuscript edit was made by this reviewer.

## T2.1 Carrier/object distinctions

The subsection now defines an object C as a pair `(m,C_0)` and explicitly writes `|C|` for its carrier. The following passages should respect that distinction consistently.

| Anchor in 08c | Current expression | Correction |
| --- | --- | --- |
| Lines 81–84 | `F(f)=γ_Y f γ_X^{-1}:D_e→D_d` | State `F(f):(1,D_e)→(1,D_d)` in C, with carrier function `|F(f)|=γ_Y f γ_X^{-1}|_{D_e}`. This separates the arrow's endpoints from the function used to represent it. |
| Lines 89–93 | `u_C=κ_m^{-1}:FQ(C)≅C` | Define `u_C:FQ(C)≅C` with carrier function the restriction of `κ_m^{-1}` to `widehat C`. The restriction is necessary because κ_m^{-1} has the larger declared domain K_m. |
| Line 119 | “The empty carrier is initial.” | Choose the object `(1,∅)` as initial. A carrier set is not itself the pair defined as an object. |
| Lines 137–143 | `Im(f)⊆D`, “enumerating C” | Let `Im(f)` be the object of the same dimension as D with carrier `|f|(|C|)⊆|D|`, and enumerate `|C|`. The factorization arrows then have categorical object endpoints as displayed. |
| Lines 242–245 | The x_i are used without a carrier range; the returned value “belongs to X” | State `x_i∈|X|`; the returned value belongs to `|X|`. |
| Lines 289–298,332 | `h_L(p,nil)`, “halting on P×W”, and `FV_Fm(s)=nil` | In the computational statements, use the empty-list value `|nil|(())` (or the fixed empty-list code 0 from §5), and the carrier `|P|×|W|`. The nil morphism has source the terminal object; it is not itself a list code. The cons expressions can use the declared `f(x)=|f|(x)` abbreviation. |
| Lines 347–353 | A label “belongs to R_n”; a “c.e. carrier P_A^all” is then used as a C-object | Use `|R_n|`; define `P_A^all` as the object of dimension one whose carrier is the c.e. set of valid derivation codes, and write `|P_A^all|` for that set. |
| Lines 361–371 | Intermediate “values in Q” and “a value in Q” | Use `|Q|`. Likewise state that the finite evaluation halts on `|P_A^all|` before declaring its categorical fold. |

These are local type/presentation defects under the explicit convention the revised text has now adopted. The intended mathematical constructions are apparent and repairable. They should not be left as implicit coercions before formalization.

## T2.2 Comparison of proof codes

At 08c lines 409–419, the text asserts the literal equality

`G_N P_T^syn = |Prf_T|`

because both constructions use the same tree constructors and omit membership witnesses. The rule-label codes must also agree. In the syntactic predicate category, iterated products and coproducts have the numerical pairing/tag presentations chosen in §5. The new numerical category chooses products by concatenating tuples, then uses κ_m to encode the resulting flat tuple. These presentations need not give equal numbers for a nested product. For example, a label in `(V×Fm)×(Tm×Tm)` can have the nested code `⟨⟨x,s⟩,⟨u,t⟩⟩`, whereas a left-associated four-tuple code can be `⟨⟨⟨x,s⟩,u⟩,t⟩`. Equality of the decoded rule instance does not make these numbers equal.

The present text specifies the same syntax codes and tree constructors but does not specify the full coincidence of all rule-label presentations. Thus the literal proof-carrier equality is not justified as written. This does not undermine equality of the sentence theorem sets: a recursive relabeling comparison suffices.

One repair is to choose the rule-label presentations, premise maps, and conclusion maps exactly as in Lemma 5.8, spelling out the comparison maps from the numerical products to those unary coded presentations. Then the same-code assertion can be proved by the stated induction.

Alternatively, give a typed computable isomorphism between the two proof carriers. At each node, apply the canonical coding isomorphism for its rule label and recursively transform its children. Its inverse uses the inverse label isomorphisms. Induction proves validity, inverse equations, and preservation of the sentence conclusion. This yields a bijection

`ρ_T:G_N P_T^syn→|Prf_T|`,

with `|c_T|ρ_T=G_N c_T^syn`, which is exactly what the subsequent image-predicate argument needs. The sentence carrier equality `G_N S^syn=|S|` remains justified by the explicit same-syntax-code choice.

This is a substantial but local comparison omission. No new set-theoretic assumption is needed. Avoid solving it by claiming that the standard interpretation preserves initial algebras: the numerical initiality proof has independently been supplied, and the desired comparison can be constructed directly.

## Checks that pass

- The Q/F equivalence now has explicit categories, object maps, morphism computations, functor equations, natural comparison directions, and the nullary tuple coding.
- The regularity proof gives a typed descent map and distinguishes regular epimorphisms from arbitrary arrows. The partial-map functor has object/arrow actions, restriction preservation, full faithfulness, and essential surjectivity.
- The parameterized syntax algebra, target algebra, folds, base equations, algebra equation, computability, halting on source carriers, and uniqueness are present. Its operations need no total extension off those carriers.
- The list target structure and fold equations are present; only the nil morphism/value notation identified above remains to be corrected.
- The substitution paragraph uses the same syntax codes and correctly distinguishes the failure-valued total map b_F from its successful restriction on Adm. Its constructor equations and use of parameterized uniqueness match Appendix A.
- The derivation target algebra, total fold, conclusion equation, algebra-morphism equation, and uniqueness are supplied. The source-carrier notation needs the local correction above.
- The numerical incompleteness subsection now explicitly defines `a=1_A,b=1_B:ω⇀ω` in Rec, types the inclusion functor, and types the final inequalities in the splitting. Its theorem application uses the required source inseparability and target domains without identifying Rec, its total splitting, and C_rec.
- The two new subsections have separate purposes: realizing Appendix A in the numerical category, then applying the incompleteness criterion there. The general Appendix A image theorem remains cited rather than reproved.

**Unresolved findings:** T2.1 and T2.2. No Lean verification, whole-paper certification, or new literature verification is claimed.
