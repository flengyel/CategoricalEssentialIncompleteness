# Numerical-foundation consolidation: dependency and type review, round 1

Scope: the proposed version-27 numerical structural proposition in `sections/08c-numerical-realization.tex`, its uses in Appendix B, and the dependent category convention in §9. I compared the working files with `tmp/consolidate27/baseline` and read `consolidation.diff`. I did not edit the manuscript or review unrelated mathematical claims.

The shared structural proof preserves the numerical obligations. Three small repairs remain in the dependent exposition of §9; no defect was found in the new partial comparison construction.

## Necessary repairs

1. In the new opening numerical-category paragraph of §9, write `objects C=(m,C_0)` before using `|C|=C_0`. The following abbreviation must be restricted to **computably enumerable** subsets `C_0` of `N^m`; its present unrestricted wording would include subsets that are not objects of the category.
2. In the paragraph defining nonempty-word codings, take `m(A)` to be the first coordinate of the object `A=(m(A),|A|)`. The old instruction to choose an ambient dimension belonged to the raw-subset presentation. An empty carrier can be a subset of several powers, so the now-fixed object coordinate should govern its code.
3. In §9's evaluation-functor subsection, replace the statement that `Q_num` is constructed in Appendix B by a reference to `prop:numerical-structure`. Appendix B now recalls this earlier construction.

## Checked interfaces

- The total equivalence retains the typed functors `Q:C_rec -> B_rec`, `F:B_rec -> C_rec`, and their decoding natural isomorphisms `u` and `v`.
- Dimension-zero coding, the terminal and initial objects, finite-limit constructions, tagged coproduct injections/copairings, typed images and the numerical mono partial inverses remain.
- Preimage search supplies the total morphism `s_q:D -> C` on the stated c.e. source carrier; `q s_q=1_D` and the coequalizer descent argument have the correct types. This is not used to assert a natural section of a fork morphism.
- `Q_num:Split(Rec) -> Par(C_rec,Mono)` sends `(X,e)` to `(1,D_e)`. For a partial split morphism `f`, the domain object `(1,U_f)` is c.e., its inclusion is monic, and its right leg is total on `U_f`.
- The displayed pullback `P_{f,g}` is a dimension-two object. Its projection and inverse `(z -> (z,hat f(z)))` are computable on their entire specified source carriers and identify the composite span with the normalized span for `gf`.
- Restriction preservation is checked by the domain span `(iota_f,iota_f)`. The comparison isomorphisms extend to partial morphisms: both naturality equations identify domains as well as values. The normalized-span equality criterion supplies equality in the partial-map category, not merely equality on defined values.
- The identities establish quasi-inverse restriction functors. They replace the duplicated equivalence proof without assuming that an equivalence has a literal inverse.
- Appendix B retains the component-image subfunctor argument, the cancellation equation proving naturality of descent, the three finite probes, and its extensivity proof. The terminal-subobject and local-connectedness arguments have not been consolidated in this task.

## Exact preservation checks

The numerical first-order proof and arithmetic proof-code comparison, beginning at `Choose the variable object V=(1,N)`, are byte-equivalent to the version-26 tail. The fork-specific block from `Limits and tagged finite coproducts` through the end of Proposition B.2's proof is also unchanged. The checked numerical-incompleteness, Miller and syntactic-realization files are unchanged at this review checkpoint. These comparisons precede any global version-metadata update.

Once the three §9 repairs are applied, the consolidation has no outstanding dependency or type issue within this scope. This is a review of the stated change, not a correctness certificate for every theorem in the manuscript.
