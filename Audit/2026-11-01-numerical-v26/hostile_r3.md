# (A) Kill-shots / hard blockers

No false main theorem is established. **One concrete typing/comparison issue remains in the node-relabeling proof.** The categorical equivalences, direct initiality arguments, retained axiom object, substitution realization, and numerical incompleteness application otherwise pass this scoped reread.

Reviewed completely: the frozen round-3 realization and incompleteness sources in `tmp/numerical26/round3/`. This report uses exact section, file, and identifying-equation anchors because the expanded PDF is being rebuilt by the parent workflow. It is an author-side audit, not formal verification.

# (B) Major weaknesses

## H10. An interpreted rule-object element is not yet the numerical label used by the syntactic proof-tree constructor

**Anchor:** §7.4, `08c-numerical-realization.tex`, paragraph starting “To compare with the syntactic category,” the declaration

`rho_n:|R_n^num| ≅ G_N R_n^syn`,

and the subsequent instruction “replace that label by `rho_n(kappa_(m_n)^(-1)(r))`.”

**Claim as written:** this replacement inserts a valid syntactic rule label into the numerical derivation-tree constructor of Lemma 5.8 and hence defines the recursive bijection rho_T.

**Failure mode:** ill_typed / missing comparison. **Evidence:** the codomain declared for rho_n differs from the scalar label presentation explicitly used in Lemma 5.8.

Lemma 5.8 chooses a Sigma_1 predicate presentation `C_n(z)` for each rule object and uses a number z satisfying that predicate as the stored node label. In contrast, `G_N R_n^syn` is the actual interpreted Set-carrier of the categorical rule object. It is not declared to equal the chosen subset of N. For example, the allowed chosen product for a generalization-rule object can have interpreted carrier `N×G_N Fm^syn`; an element is a tuple, whereas the tree constructor expects one numerical label. The new rho_n is correctly typed as a comparison with that actual Set-carrier, but its value cannot be inserted into the scalar constructor without an additional presentation map.

This is not resolved merely by saying that tuple/tag recoding is computable: the actual target of the next insertion must be specified. Choose the exact presentation isomorphism

`u_n:J_PA(C_n) ≅ R_n^syn`

used in the Lemma-5.8 construction. Then

`eta_n=G_N(u_n):C_n(N) ≅ G_N R_n^syn`

has a declared numerical subset as its source. The stored syntactic label is

`eta_n^(-1) rho_n kappa_(m_n)^(-1)(r)`;

the inverse numerical stored label is

`kappa_(m_n) rho_n^(-1) eta_n(z)`.

The existing premise/conclusion comparison equations through rho_n then prove that these label conversions preserve validity and conclusions, and nodewise induction gives the stated recursive proof-carrier bijection. No literal equality of the two proof carriers is required.

**Downstream impact:** the conclusion-image equality and the final reduction inequalities use rho_T. **Severity:** major but local typing omission, repairable by these explicit chosen presentation maps. No counterexample to numerical realization or incompleteness is claimed.

# (C) Minor issues

In the generic derivation evaluation paragraph, “Together with the node's rule label” should read “Together with the decoded rule instance.” The stored numerical label belongs to the coded carrier; the algebra operation is defined on the actual rule-object carrier. The preceding validity paragraph already introduces the decoding, so this is a local clarification of its use rather than a new mathematical obligation.

No other necessary wording correction was identified in this reread. The empty-list element, object/carrier notation, example operation source conditions, and list slice-product comparison have been corrected explicitly.

# (D) Cross-section consistency failures

All earlier findings have been materially addressed:

- **H1:** Q and F have typed object and arrow actions; their inverse comparisons and naturality equations are stated. The monic-span comparison has explicit arrow action, functor/restriction laws, fullness, faithfulness, and essential surjectivity.
- **H2:** syntax, list, and derivation algebras have their structure maps, arbitrary target structures, fold endpoints and equations, direct halting arguments on specified carriers, and uniqueness proofs.
- **H3/H6:** separate syntactic and numerical carriers and conclusion maps are named; the new rule comparisons and proof relabeling have the correct intended role. H10 is the remaining presentation step required to make the relabeling typed.
- **H4:** substitution is explicitly term-valued and option-valued as appropriate, with the admissibility pullback and the numerical constructor equations identified by direct induction and uniqueness.
- **H5:** the original A is retained in the generic inference functor, avoiding a change of coefficient. The arithmetic specialization separately chooses its sentence-code axiom inclusion.
- **H7:** interpreted underlying functions and categorical arrows are separated; image objects have dimensions and carriers; the remaining numerical memberships use carrier notation.
- **H8:** the function-operation source now includes p in |P| and every child value in |X|, including the nullary case.
- **H9:** the canonical isomorphism from the list's slice-product source to V×Z and its inverse are written.

The category regularity proof uses computable carrier constructions and dovetailed preimage search. The initiality proof applies arbitrary partial-recursive algebra operations only to carrier inputs supplied by induction; it does not add an ambient total-extension assumption. The split separates construction of the numerical realization from its incompleteness application. Appendix A's image/leastness theorem remains invoked by reference, without another copy of its general proof.

The incompleteness subsection has the correct types for I, J_rec, a,b, I(a),I(b), theta, nu, and the restriction inequalities. Once H10 makes the proof-image comparison explicit, the application of the earlier diagonal-domain lemma and categorical corollary has no additional identified defect.

# (E) Acceptance conditions, non-negotiable

1. Specify the exact numerical predicate presentation of each syntactic rule object used by Lemma 5.8, its interpreted presentation isomorphism, and the resulting scalar node-label conversion in both directions. This must type the construction of rho_T.
2. Use the decoded rule instance in the generic algebra-evaluation paragraph.
3. Preserve the now-explicit fold structures, carrier conditions, and comparison equations while making these local corrections.

A final reread of the corrected source is sufficient to check these endpoints. No new theorem or weakened claim is requested.

# (F) Not checked / uncertainty log

The two revised subsections and their code/comparison interface were read completely. The precise numerical label convention was checked against Lemma 5.8 and the chosen predicate-category equivalence, rather than inferred from a generic Set interpretation. The relevant earlier appendix and syntactic definitions were inspected in the first two rounds. This report does not re-audit the complete manuscript or literature, and it performs no Lean checking. Final compilation and visual layout inspection belong to the parent workflow.

**Strongest confirmed blocker:** H10 inserts an element of the actual interpreted rule-object carrier where the proof constructor requires a scalar predicate-presentation label.

**Strongest suspected unconfirmed blocker:** none; the explicit presentation-map repair supplies a complete route through the remaining issue.

**Most important thing not checked:** unrelated earlier constructions and later applications have not been re-proved in this round.

**Dependence on unavailable material:** none.

**Final recommendation:** unknown for whole-paper publication; **local acceptance withheld pending H10 and the decoded-label clarification**, with all earlier concrete repairs verified.
