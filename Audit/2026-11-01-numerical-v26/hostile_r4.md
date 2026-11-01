# (A) Kill-shots / hard blockers

None established. **PASS for the revised numerical realization and numerical incompleteness subsections, §§7.4–7.5, within the scope of this audit.** No concrete mathematical, typing, or dependency finding remains unresolved.

Final reviewed sources in `tmp/numerical26/round4/`:

| File | SHA-256 |
| --- | --- |
| `08c-numerical-realization.tex` | `28e6178cc451e2ff0de868c7c43872740d23d8dad74d337db3c96c7bb540378a` |
| `08d-numerical-incompleteness.tex` | `11d6c06139fa1b2b457d3c1a577026767afae0cd2121005eac5c3ef1ed9d98f8` |
| `08-essential-incompleteness-of-arithmetic.tex` | `a67c80632f8729caa0d0679e5b8bab260a5cdc4b20636ec9399ddb23ebdc247f` |

This is an author-side mathematical and typing audit of the named text and its inspected dependency interfaces, not a whole-paper publication decision or Lean verification.

# (B) Major weaknesses

None confirmed in the final text. The preceding review's scalar-label finding H10 is closed by the explicit predicate presentations and interpreted isomorphisms described below.

The numerical category is specified using dimension/carrier pairs and computable underlying functions. The total comparison Q and its quasi-inverse F have typed object and arrow actions through the chosen numerical codings. The inverse comparisons have component types and naturality equations. The proof of regularity uses actual c.e. carrier constructions, computable pairing/restriction, and dovetailed preimage search for coequalizer descent. Monomorphism inverses are computed on their image carriers. The monic-span comparison explicitly identifies domains and values and proves the functor and restriction laws, fullness, faithfulness, and essential surjectivity.

The syntax, list, and derivation initiality arguments quantify over arbitrary algebras of the correct slice types. Each fold has its source, target, projection or conclusion condition, and algebra equation stated. Structural induction proves that the chosen partial-recursive operation programs halt on the specified valid inputs; it does not require total extensions outside their carriers. The same constructor decomposition proves uniqueness. These are direct universal-property proofs in the numerical category rather than an unsupported claim that a regular interpretation functor preserves initial algebras.

The generic inference construction retains its original axiom object A and decodes the stored scalar label into an element of the corresponding rule carrier before applying the rule maps or target algebra operation. Thus the proof concerns the originally stated H_A. The numerical substitution algorithms realize the declared term-valued and option-valued morphisms, and the admissibility subobject is their stated success pullback. Appendix A's least-image result is invoked at the point of application without duplicating its general proof.

# (C) Minor issues

No necessary correction remains. The earlier imprecise carrier descriptions, missing nullary parameter condition, implicit list source comparison, and undecoded rule-label phrase are all repaired in the final snapshot.

No further change is proposed merely to produce another revision. The explicit comparison data and fold equations perform mathematical work and should be retained.

# (D) Cross-section consistency failures

None found in the final realization/application interface.

## Closure of H10 and the standard proof-code comparison

The final paragraph introducing the rule comparison now distinguishes all four types:

- the numerical rule-object carrier `|R_n^num|`;
- its stored scalar encoding `widehat(R_n^num)`;
- the actual interpreted Set-carrier `G_N R_n^syn`;
- the scalar predicate carrier `C_n(N)⊆N` used in Lemma 5.8's syntactic proof-tree construction.

The comparison `rho_n:|R_n^num|≅G_N R_n^syn` has its premise/conclusion equations, including the finite-product comparison chi_n. The manuscript then chooses the exact predicate presentation `u_n:J_PA(C_n)≅R_n^syn` used by the derivation construction and sets

`eta_n=G_N(u_n):C_n(N)≅G_N R_n^syn`.

The representing programs of u_n and its inverse make both directions computable on their specified carriers. The stored-label conversion has the well-typed path

`widehat(R_n^num) → |R_n^num| → G_N R_n^syn → C_n(N)`,

given by `eta_n^(-1) rho_n kappa_(m_n)^(-1)`. Its inverse has path

`C_n(N) → G_N R_n^syn → |R_n^num| → widehat(R_n^num)`,

given by `kappa_(m_n) rho_n^(-1) eta_n`.

Both labels inserted into the tree constructors are therefore numbers of the required presentation. The rule comparison equations imply preservation of premises and conclusions. Induction on tree size proves validity preservation and the two inverse equations for the nodewise relabelings. The constructors are the same canonical finite-tree constructors and witnesses are not part of a derivation label, so no additional witness choices affect this bijection. Restriction to sentence conclusions gives the stated computable rho_T and its conclusion equation. The proof images consequently agree even though the proof carriers are not asserted literally equal.

## Remaining interfaces

| Interface | Final check |
| --- | --- |
| Object versus carrier | F(f) and its underlying function are distinguished; image objects have a declared dimension and carrier; numerical memberships use carrier notation. |
| Parameterized syntax | p belongs to |P|, symbols to their coefficient carriers, and child values to the appropriate carrier/fiber. This covers nullary operations, including empty P. Fold equations are in the declared product of slice categories. |
| Lists | The canonical isomorphism `(P×V)×_P Z≅V×Z` and its inverse justify the cons-operation type. The empty-list value is distinguished from its constructor morphism. |
| Generic derivations | A is retained; stored labels are decoded; c_all and delta_A are declared; arbitrary beta and the unique slice fold have explicit types and equations. |
| Sentence theory | The sentence proof map is the pullback of the full conclusion map. Its image is the least sentence theory by Appendix A, and the partial inverse/image-range lemma supplies the range idempotent after transport by Q. |
| Numerical/syntactic bridge | Equal syntax codes and the computed rule/proof relabelings identify conclusion images. The final application needs this image comparison, not literal identity of all code presentations. |
| Numerical incompleteness | The Rec arrows a,b and the splitting arrows I(a),I(b) are distinguished. J_rec has its stated action; the source reversed conditional is computable; fullness preserves inseparability on the original object. The three reduction inequalities have their correct ambient objects, and the categorical incompleteness corollary is applied with the required disjointness and inverse-image join properties. |

The two subsections have distinct purposes. Section 7.4 constructs and compares the numerical realization; §7.5 applies it to incompleteness. No initial-algebra preservation principle is smuggled into this application, and the range/image construction remains categorical at its declared category type. External tuple sets, codes, and models occur in the explicit numerical interpretation.

# (E) Acceptance conditions, non-negotiable

All concrete acceptance endpoints from the previous rounds are met:

1. The categorical equivalences and their computational comparison data are explicit.
2. Arbitrary target algebra operations and the unique folds are typed and used only on their proper source carriers.
3. The generic axiom object is retained in H_A.
4. The numerical, interpreted, and scalar predicate rule labels are connected by explicit computable isomorphisms before tree relabeling.
5. The sentence pullback, image/range identification, and numerical incompleteness application use those comparisons at their stated types.

No further identical review cycle is required to close an identified finding from this audit.

# (F) Not checked / uncertainty log

The final changed comparison paragraph and its two conversion formulas were checked directly against the preceding typed rule equations and Lemma 5.8's scalar label convention. Both final subsections were reread, and the round-3-to-round-4 source difference was inspected: it adds the predicate-presentation bridge and changes the algebra input phrase to “decoded rule instance.” The other proofs and interfaces were fully inspected in the earlier rounds and remain as recorded there.

This review does not certify every theorem or bibliography entry of the complete manuscript, novelty, or a Lean formalization. No Lean elaboration or kernel check was performed. The parent workflow handles final compilation and rendered-page inspection; this report's acceptance concerns the exact source hashes above.

**Strongest confirmed blocker:** none in this scoped final text.

**Strongest suspected unconfirmed blocker:** none identified.

**Most important thing not checked:** unrelated manuscript results and the full imported syntax/soundness development were not re-proved in this final round.

**Dependence on unavailable material:** none for the scoped conclusion.

**Final recommendation:** unknown for a whole-paper publication decision; **PASS for the revised §§7.4–7.5**, with all concrete findings from rounds 1–3 resolved.
