# Theorem 5.3 proof outline against manuscript v58

Target: thm:associated-incompleteness, under the standing Section 5
hypotheses. This outline was written before implementation. The separate complete-statement
Checks module validates the transported types and arbitrary-extension quantifier;
integration verification is recorded separately. The base
presentation is the existing FirstOrderPresentation, with proofs and
initiality ONLY at axiom subobjects. Arbitrary axiom morphisms continue to
use FirstOrderReflection.presentationGeneration through their regular image.

1. Identify the systems. Use the literal firstOrderRules for the base
presentation and its finite-limit transport under constantFamilyFunctor U.
Slice sentence object is exactly U x S -> U; negation is B.map nu. Slice
initial derivation families are quantified over ALL subobjects of that
sentence family. V46FirstOrderRuleTransport constructs the rule morphism.
For evaluation, use E = Over.pullback point >> Over.forget terminal and
explicit E B ~= Id components; translate the evaluated rule labels back
through that retraction. Reuse actual partial-slice comparisons rather than
redefining the existing AssociatedCategory.evaluation.

2. Closure. V46ClosedTheoryTransfer proves Gen(image A) <= image(Gen A)
using target initiality into the transported closed formula image, with no
assumption that either functor preserves initiality. Constant closure is
already constructed. For evaluation into the ORIGINAL calculus, compose
V46FiniteRuleTransport.map_closed with a RulePresentation.Translation whose
formula map is the inverse retraction component and use its closed_pullback.
The nullary axiom component is the actual pullback of E(W.arrow); unary and
binary components are inverse retraction components followed by E of the B
product comparison. Initiality in the original calculus then folds into
that reindexed closed formula subobject. Sentence pullback identifies the
result as E(W). W is arbitrary, not assumed to be a constant family.

3. Consistency and completeness. Derive a lattice order isomorphism between
subobjects of an Over object and subobjects of its underlying object. In this
coordinate, B on subobjects is pullback along the second product projection,
and E on arbitrary slice subobjects is pullback along the point-fiber map.
Use SubobjectPredicates.pullbackHom for bottom, meet, join and top, and the
explicit negation square for refutation. Derive these conclusions; do not
supply preservation or extension transport as hypothesis fields. Regular
image comparison for arbitrary presentations uses proved stable regular epi
base change and existing DeductionComparison.image_presentation.

4. Full quantifiers. For a consistent base closed theory u, prove the
associated theory consistent. A base closed consistent complete extension
maps by B to such an extension. Given ANY closed consistent complete W
above B(u) in the slice, the closure construction in step 2 and lattice
facts in step 3 give a closed consistent complete E(W) above u, using
E B ~= Id for the base inclusion. Contradict the base essential-
incompleteness quantifier. Conversely map each base extension by B and
apply the slice essential-incompleteness quantifier. Relate the generic
formulas to existing FirstOrderPresentation.EssentiallyIncomplete, not a
replacement property restricted to constant extensions.

5. Final reduction. Reuse AssociatedCategory.extension_inseparable and
no_total_extension_of_reduction, and the existing theorem-extension /
Corollary 4.3 machinery, to show every consistent closed extension of u is
incomplete. Apply the full equivalence at each consistent u >= t, obtaining
both essential incompleteness of its associated theory and the proved
no-total-extension statement. Combine with the existing Boolean equivalences
in an independent check of the COMPLETE printed theorem.

Statement-check obligations before claiming completion: the back-transport input
must be (W : Subobject (B.obj S)) with its slice closedness proof and no
constant-family witness; its output must lie in the ORIGINAL P.Theories.
Check all initiality binders are Subobject-indexed, no preservation or
incompleteness fields are introduced, and the three permitted axioms are
the complete transitive union. Keep the 5.3 row open until every clause passes.

Coordinate comparison constructed after the first integration checkpoint:
`AssociatedSliceCoordinates.comparison` relates the chosen categorical
products to the restriction products of the existing actual constant functor.
`theory_value` identifies the theorem family, `actual_map` checks its total
morphisms, and `evaluation_total` checks the actual evaluation functor on
them. The independent checks include the existing `sourceTheory` morphism.
