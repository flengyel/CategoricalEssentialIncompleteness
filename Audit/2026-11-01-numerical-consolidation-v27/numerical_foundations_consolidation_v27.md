# Numerical foundations: version 27 consolidation

The numerical foundations now have one proof in §7.4. Proposition 7.7 establishes the numerical category and its structural equivalences. Proposition 7.8 retains the complete first-order realization from the former combined proposition. Appendix B cites the shared numerical results and retains its additional fork-category arguments. No application has been removed.

The manuscript is *Logical consequence and essential incompleteness in recursion categories*, version 27, 1 November 2026. The baseline is version 26 at commit `7bf0de04ea162f5cd05688e869380aa1e412ae29`; that commit contains the unchanged version-26 manuscript and its scope audit.

## Argument and locations

| Location | Mathematical purpose |
| --- | --- |
| §7.4, p.36 | Define `Rec`, the category of pairs `(m,C_0)`, carrier notation and tuple codings. |
| Proposition 7.7, pp.36–39 | Prove the total equivalence, numerical regularity, coproduct properties, mono partial inverses and the restriction equivalence in both directions. |
| Proposition 7.8, p.39 | Prove parameter-stable syntax and list initiality, substitution and initial derivations. The first-order proof and following arithmetic code comparison are unchanged. |
| §9, pp.50–51 | Use the same numerical category, with an explicit object/carrier abbreviation, component subfunctors, and the existing object dimension. Reference the shared numerical comparison. |
| Proposition B.2, p.66 | Cite the numerical foundation; retain component images, natural descent, finite probes and extensivity for the fork category. |
| Appendix B, p.72 | Use the shared `Q_num` equivalence and identify its total restriction through the canonical isomorphism of total categories. |

## The combined proof

The proof retains §7.4's explicit dimension/carrier convention, the zero-dimensional singleton, fixed tuple codings, tagged coproduct injections and copairing, typed image factorization, and partial inverses of numerical monomorphisms. It incorporates Appendix B's computable section `s_q:D -> C` of a numerical surjection `q:C -> D` and uses it to prove kernel-pair descent.

The total comparison functors `Q` and `F` and their natural isomorphisms remain. The monic-span functor `Q_tilde` is accompanied by an explicit quasi-inverse `Q_num`. For a partial split morphism `f:(X,e) -> (Y,d)`, its image is the span

`(1,D_e) <- (1,U_f) -> (1,D_d)`,

where `U_f` is the c.e. domain of the conjugated numerical partial function. The proof checks identities, the pullback defining composition and preservation of restrictions. Both comparison naturality equations are checked for partial morphisms by their exact domains and values. These data replace the second proof of the numerical equivalence in Appendix B.

The numerical section argument does not replace the fork-category descent proof. The latter still proves naturality of the descended transformation by cancelling a surjective component. Its finite probes and tagged-subfunctor arguments also remain.

## Local review and repairs

Independent agents applied the HostileRefereeGPT and Mathematical Writing skills and checked explicit types and dependencies. The writing review consulted Knuth, Larrabee and Roberts, *Mathematical Writing*, §1, especially items 10–15 and 26. The consolidation and its affected uses were reviewed; this was not a new whole-paper review.

| Finding | Repair |
| --- | --- |
| The total restriction of `Q_num` has literal target `Tot(K_rec)`. | State the canonical isomorphism `Tot(K_rec) ≅ C_rec` before identifying the restriction with `F`. |
| A represented partial morphism was evaluated without declaring the notation; a second span used an undeclared middle object. | Declare `k(x)` and display the second typed span. |
| The cosheaf section's previous raw-subset presentation no longer matched the shared pair objects. | Specify the c.e. object/carrier abbreviation, type the component subfunctors, and take `m(A)` to be the object's first coordinate. |
| One existing phrase used “universal arrows”. | Use “universal morphisms”. |

The second local reviews record no outstanding necessary correction within their scope. The review records contain the initial findings and their closure. They do not assert verification of every theorem or of Lean code.

## Verification and preserved scope

The main document and standalone Appendix A compile. The final logs contain no undefined references, undefined citations or overfull boxes. The inspected renderings cover the shared numerical proof and transition to the realization, the changed cosheaf setup, both Appendix B citations, and the version displays.

The resulting manuscript has **78 pages**; the standalone appendix has **10 pages**. The explicit quasi-inverse and its partial naturality data account for additional exposition. No page-reduction claim is made.

The first-order realization proof and following arithmetic proof-code comparison are unchanged byte for byte. The fork-specific portion of Proposition B.2's proof is also unchanged. The syntactic realization, model soundness, arithmetic application, indexed families, Miller application, cosheaf application, and Appendices A, C and D remain. The abstract and introduction are unchanged. Appendix A's standalone exports have version-27 metadata; its mathematics is unchanged.

Only the numerical-foundation consolidation and the changes needed for its uses have been implemented. The separate local-connectedness and categorical-distinction repetitions identified in the scope audit have not been consolidated. No Lean source was changed or tested.
