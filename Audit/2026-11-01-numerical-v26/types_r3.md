# Numerical realization: third type review

**Disposition: one numerical-label type correction remains.** The carrier/object corrections from round 2 are implemented. The proof-carrier comparison now has the right form of a computable relabeling bijection, but its forward procedure inserts an element of an interpreted rule object where a scalar numerical label is required.

Reviewed snapshot: `tmp/numerical26/round3/08c-numerical-realization.tex` (SHA-256 `8c9c839bf5ad31fbfb791c17a2e3c99763e68f43f27713393a22d68dcddd0ceb`) and `08d-numerical-incompleteness.tex` (SHA-256 `11d6c06139fa1b2b457d3c1a577026767afae0cd2121005eac5c3ef1ed9d98f8`), with the containing arithmetic source. They matched the working source at the time of the check.

## T3.1 Interpreted rule elements and stored numerical labels

At `08c`, lines 442–443, the map

`ρ_n:|R_n^num|≅G_N R_n^syn`

has an interpreted categorical carrier as its codomain. This need not be a subset of N: a rule object formed as a product can interpret as a product of sets. At lines 458–460 the procedure inserts `ρ_n(κ_{m_n}^{-1}(r))` directly into the derivation-tree constructor as its stored label. The constructor of Lemma 5.8 instead stores a scalar label in the chosen Σ₁ predicate presentation of the rule object. Those types are different.

Name that presentation explicitly: choose the predicate `C_n(z)` and the isomorphism `u_n:J_PA(C_n)≅R_n^syn` used to transport the rule maps in Lemma 5.8. Its interpretation is a computable bijection

`η_n:C_n(N)≅G_N R_n^syn`,

where `C_n(N)⊆N` is the scalar-label carrier. The numerical-to-syntactic stored-label conversion is then

`η_n^{-1}ρ_nκ_{m_n}^{-1}`,

and its inverse is `κ_{m_n}ρ_n^{-1}η_n`. Both directions have scalar numerical source and target. The rule-comparison equations already given in the manuscript then prove validity and conclusion preservation using the transported rule maps of the chosen predicate presentation.

This is a local comparison omission, not a counterexample to the existence of a computable proof-carrier bijection. It must be corrected before the displayed recursive procedure is well typed.

## Closed findings and retained checks

The explicit images and initial object, carrier functions of F(f) and u_C, syntax-algebra input/output carriers, empty-list value, and derivation-object and evaluation-carrier declarations now respect the adopted object/carrier distinction. The category comparisons, regularity, arbitrary-algebra syntax/list/derivation folds, substitution realization, sentence pullback, and numerical incompleteness application remain as checked in the preceding reports. No additional defect was identified in those passages. The new proof-carrier comparison correctly avoids claiming literal equality between alternative rule-label codings; only the scalar-label interface above remains missing.

No manuscript edit, Lean verification, new literature verification, or whole-paper certification was performed by this reviewer.
