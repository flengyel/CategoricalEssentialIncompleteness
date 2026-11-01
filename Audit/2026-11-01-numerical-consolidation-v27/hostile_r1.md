# (A) Kill-shots / hard blockers

No false statement or mathematical blocker was found in the one numerical-foundation consolidation. This is an author-side review of the source snapshot, not a journal report or a new correctness certificate for the whole paper.

Scope: §7.4's new `prop:numerical-structure`, the separation of the retained first-order realization, the numerical references in Appendix B, and the category/carrier convention at the start of §9. The comparison is against `tmp/consolidate27/baseline`. PDF pagination of the edited snapshot was not yet available, so anchors below are section and exact source-line locations.

The numerical section proves the structural facts once. The first-order realization and proof-code comparison remain. Appendix B retains the new arguments for the functor category; it does not infer natural sections from the existence of numerical sections.

# (B) Major weaknesses

None established within this scope. The construction of the reverse partial-map functor now includes its actual monic-span representatives and naturality checks on arbitrary partial morphisms. The two comparison functors are shown to be quasi-inverse; no literal inverse of an equivalence is presumed.

# (C) Minor issues

## M1. State the canonical total-category identification in the Appendix B reference

- **Anchor:** Appendix B, `b-three-point-cosheaves.tex:594–595`: “Its restriction to total categories is the equivalence `F:B_rec→C_rec` there.”
- **Claim as written:** the restriction of `Q_num:Split(Rec)→K_rec` is literally a functor with codomain `C_rec`.
- **Failure mode:** `inconsistent_use` of the codomain, minor.
- **Evidence:** structural argument. The literal restriction has type `Tot(Q_num):B_rec→Tot(K_rec)`. Its composite with the canonical isomorphism `Tot(Par(C_rec,Mono))≅C_rec` is `F`. Section 7.4 itself states the relationship correctly at lines237–238, using the canonical inclusion into `K_rec`.
- **Downstream impact:** no mathematical conclusion fails, but the type stated in the cross-reference suppresses the category identification.
- **Repair:** say that the total part, followed by the canonical isomorphism from `Tot(K_rec)` to `C_rec`, is `F`.

## M2. Use carriers in the subfunctor definition

- **Anchor:** §9, `09-three-point-space.tex:55–56`: “c.e. subsets `D_j⊂Y_j` such that `r_i^Y(D_0)⊂D_i`.” Lines49–51 have explicitly typed `Y_j` as objects of `C_rec`.
- **Claim as written:** the component objects are used directly as sets in this definition.
- **Failure mode:** `ambiguous`, minor.
- **Evidence:** absence of an exact carrier declaration for this particular subset notation. The new shorthand at lines44–46 expressly mentions writing a named carrier for a pair and elementwise computations, but does not expressly define subset notation between named component objects.
- **Downstream impact:** the intended restricted functor is recoverable, and the fork proofs do not become false; the definition nonetheless mixes the displayed object and carrier types.
- **Repair:** define the component carrier inclusions as `|D_j|⊂|Y_j|`, with the same ambient tuple dimension, and use `|r_i^Y|(|D_0|)⊂|D_i|`. The components of the subfunctor are the corresponding numerical objects and the restricted morphisms. An equally explicit declared convention for all such carrier operations would also repair this point.

# (D) Cross-section consistency failures

Apart from the two minor typing points above, no cross-section inconsistency was found. The following interfaces were checked.

| Interface | Typed construction and law checked | Result |
| --- | --- | --- |
| `Q:C_rec→B_rec` | Codes the source carrier by fixed tuple coding; source semidecision makes its domain exact. Identity and composition follow from decoding equations. | Preserved from §7.4. |
| `F:B_rec→C_rec` | `(X,e)↦(1,D_e)` and total split morphisms to their conjugated functions. Totality is the equation `bar f=e`; target membership uses `f=dfe`. | Well typed. |
| Numerical regularity | A surjection `q:C→D` has computable `s_q:D→C`; `q s_q=1_D`. For a kernel-pair-constant `h:C→Z`, `d=h s_q:D→Z` satisfies `d q=h`, and surjectivity proves uniqueness. | The section argument from Appendix B is incorporated without losing the original image factorization or pullback-stability proof. |
| `Q_tilde:Par(C_rec,Mono)→Split(Rec)` | `(C←m B→g D)↦Q(g) μ_m`. The inverse-search equations make `μ_m` a partial inverse on the coded image. Pullback composition and function composition select the same pairs and values. | Well defined on isomorphism classes of spans and preserves restrictions. |
| `Q_num:Split(Rec)→Par(C_rec,Mono)` | `(X,e)↦(1,D_e)`; `f↦[(1,D_e)←(1,U_f)→(1,D_d)]`. The left leg is inclusion, the right leg is total on `U_f`, and the exact domain is c.e. | Both legs are numerical morphisms; identities and restrictions are checked. |
| Composition of `Q_num` | The pullback object `P_(f,g)=(2,{(z,w):z∈U_f,w∈U_g,hat f(z)=w})` is computably isomorphic to `(1,U_(gf))` by first projection, with inverse `z↦(z,hat f(z))`. | Both functions are total on the specified carriers; the span legs commute. |
| Natural comparison `u:Q_num Q_tilde⇒1` | For any partial `k:C⇀D`, the two composites out of `FQ(C)` have exactly the points whose decoded values lie in the domain of `k`; their values agree. Equal represented domains and values give a computable isomorphism of middle objects. | Checked for partial morphisms, not only totals. |
| Natural comparison `v:Q_tilde Q_num⇒1` | For partial `a:(X,e)⇀(Y,d)`, both composites are defined exactly on `U_a⊂D_e` and have value `a(γ_X^{-1}(z))`. | Checked for partial morphisms. |
| Appendix B's numerical use | The two repeated numerical proofs become references to the shared proposition. The component-image subfunctor argument, surjective descent equation, finite probes, and extensivity proof remain. | Dependencies preserved. |

The fixed recursive bijection `γ_ω=1_N` is explicitly given in §5, lines18–25; the comparison formulas also use `κ_1=1_N`, fixed in §7.4, line33. Thus the object and domain identifications in the naturality checks are supplied by the manuscript.

A direct source comparison verified that the numerical first-order realization and code-comparison tail beginning “Choose the variable object” is unchanged. A second comparison verified that Appendix B's entire fork-specific proof from “Limits and tagged finite coproducts” through the extensivity conclusion is unchanged. No application or counterexample is removed.

# (E) Acceptance conditions, non-negotiable

1. **Cross-reference type:** repair M1 so the literal target of the restricted functor is stated before or through the canonical identification. This is necessary for the requested explicit-type standard, not a theorem-level rejection.
2. **Component carriers:** repair M2 by typing the carrier inclusions and restricted morphisms. This is necessary for an unambiguous category definition.
3. **Preserved application proofs:** retain the first-order realization/code-comparison tail and the fork-specific naturality, probe and extensivity arguments already verified in this snapshot. Removing them would reject this as a dependency-preserving consolidation.
4. **Build endpoint:** compile the exact final source and resolve the new structural-proposition references and resulting numbering. This reviewer has not performed that build; an unresolved label would prevent delivery as a checked document.

# (F) Not checked / uncertainty log

The source proof of the numerical structure, all new partial-functor data and naturality equations, the changed Appendix B interfaces, and the changed §9 convention were read. The relevant old proof blocks and retained tails were compared. This review does not re-prove the unchanged initial-algebra constructions, soundness, arithmetic, Miller, cosheaf Turing morphism, completion theorems or incompleteness applications. No literature novelty claim, Lean elaboration or rendered layout was checked.

**Strongest confirmed blocker:** none at theorem level; two minor explicit-typing repairs remain.

**Strongest suspected unconfirmed blocker:** none promoted to a finding.

**Most important thing not checked:** compilation and rendering of the final edited source.

**Dependence on unavailable material:** none for the local mathematical conclusions; final PDF locations await the build.

**Final recommendation:** unknown for publication. Within the one-consolidation scope, no mathematical reconstruction is needed; apply M1 and M2 and complete the build endpoint.
