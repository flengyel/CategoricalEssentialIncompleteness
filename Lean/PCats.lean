/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import PCats.Restriction
public import PCats.PCat
public import PCats.HellerNaturalizer
public import PCats.Erratum
public import PCats.DomSemilattice
public import PCats.Unions
public import PCats.Ranges
public import PCats.Coproducts
public import PCats.NCoproducts
public import PCats.CountableUnions
public import PCats.Domains
public import PCats.DomProducts
public import PCats.DomSubdomains
public import PCats.DomSubdomainMorphisms
public import PCats.DomEqualizers
public import PCats.DomPullbacks
public import PCats.DomTotalEmbedding
public import PCats.Recursion
public import PCats.Dominical
public import PCats.DominicalRecursion
public import PCats.OptionKleisli

/-!
# Appendix A of the Rice-Shapiro paper

Formalization of Appendix A of "Countable Extension Families and a
Quotient-Fibration Form of the Rice-Shapiro Theorem".

Root module: imports the library modules. New material goes in a new module,
not here.

* `PCats.Restriction` — restriction categories, total morphisms (A.1, A.3)
* `PCats.PCat` — `P`-categories, induced restriction, domain calculus (A.2, A.3)
* `PCats.HellerNaturalizer` — Heller's projection-generated subcategory `P`
  and the two naturalizer containments (A.2, lines 58–62)
* `PCats.Erratum` — Lemma A and Corollary B of the APAL 2004 erratum
* `PCats.DomSemilattice` — the meet-semilattice `Dom(X)` of domains on an object (A.3)
* `PCats.Unions` — unions and stable unions of countable families of domains
* `PCats.Ranges` — ranges, `rP`-categories, sections, choice (A.4)
* `PCats.Coproducts` — coproducts, `P⁺`-structure, distributivity (A.2)
* `PCats.NCoproducts` — `ℕ`-ary coproducts and countable distributivity
* `PCats.CountableUnions` — ranges of countable copairings are stable unions
* `PCats.Domains` — the category of domains `Dom C`, Lemma A.4 (A.5)
* `PCats.DomProducts` — the product object, restricted projections, lift, and
  direct universal property in `Dom C`, the binary-product clause of Rosolini
  Thm. 2.3.3 (A.5)
* `PCats.DomSubdomains` — subdomains, their inclusions, closure under
  composition, inverse images along a morphism of `Dom C`, and the comparison
  isomorphism with an inverse image along an isomorphism; the
  composition-of-subdomains and inverse-image clauses of Rosolini
  Thm. 2.3.3 (A.5)
* `PCats.DomSubdomainMorphisms` — the identity subdomain and the family of
  morphisms of `Dom C` isomorphic over a fixed codomain to a canonical
  subdomain inclusion, with its identity, composition, and pullback
  closure (A.5)
* `PCats.DomEqualizers` — the diagonal range subdomain and the explicit
  equalizer of a parallel pair in `Dom C` under ranges, the equalizer clause of
  Rosolini Cor. 2.4.10 (A.5)
* `PCats.DomPullbacks` — the pullback of an arbitrary cospan in `Dom C` under
  ranges, as the equalizer of the two composites out of the binary
  product (A.5)
* `PCats.DomTotalEmbedding` — binary products in the wide subcategory of total
  morphisms, the full and faithful embedding into `Dom C`, and its preservation
  of binary products, Rosolini Thm. 2.3.2 (A.5)
* `PCats.Recursion` — prodominical isotypes, Turing morphisms (A.6)
* `PCats.Dominical` — Di Paola–Heller totality, the dominical axioms N1–N4,
  the induced `P`-category, and Lemma 3.5(iii)
* `PCats.DominicalRecursion` — zero absorption from N1, fixed-source Turing
  data, the transport at A.6, lines 381–388, and Prop. A.5
* `PCats.OptionKleisli` — the Kleisli category of `Option`, a concrete instance

Of Rosolini Thm. 2.3.3 the binary-product, inverse-image, and
composition-of-subdomains clauses for `Dom C` are formalized directly.
`Dom.subdomainMorphisms` is the family of morphisms isomorphic over a fixed
codomain to a canonical `Subdomain` inclusion; every member is monic,
membership is invariant under a source isomorphism over the fixed codomain,
the family contains the identities and is closed under composition, and
`Dom.instIsMultiplicativeSubdomainMorphisms` records those last two facts. The
composition proof transports a representative along
`Dom.Subdomain.inverseImageIso`. By
`Dom.exists_pullback_of_mem_subdomainMorphisms` every member has a pullback
along an arbitrary morphism whose base-changed leg is again a member, with the
square and the `∃!` universal property stated directly. The existential theorem
does not define a choice of pullback objects or legs, and no
`Limits.HasPullbacks` or base-change instance is declared. This is distinct
from `Dom.Subdomain.inverseImage_existsUnique`, the canonical-inclusion case
its construction uses.

Together with the direct binary products in `Dom C`, these results establish
the defining conditions for Rosolini's dominion: `Dom.subdomainMorphisms` is a
source-isomorphism-saturated family of monomorphisms, contains the identities,
is closed under composition, and admits a pullback representative in the family
along every morphism. No bundled Lean definition or structure for dominions is
provided. Rosolini's induced embedding of `C` remains unformalized.

Under `HasRanges`, `Dom C` has equalizers: `Dom.equalizerObject` and
`Dom.equalizerInclusion` are Rosolini's construction, the inverse image of the
diagonal range subdomain along the pairing of the two arrows, and
`Dom.equalizer_comm` with `Dom.equalizer_existsUnique` is the universal
property stated directly.

`PCats.DomPullbacks` combines the two: under ranges, `Dom.pullbackObject f g`
is the equalizer of `binaryProductFst A B ≫ f` and `binaryProductSnd A B ≫ g`,
with legs `Dom.pullbackFst` and `Dom.pullbackSnd`, commutativity
`Dom.pullback_comm`, and the universal property `Dom.pullback_existsUnique`.
`Dom.exists_pullback_of_mem_subdomainMorphisms` is a separate result, requiring
no ranges and applying when one leg of the cospan lies in
`Dom.subdomainMorphisms`.

`Dom.rangeLiftPullback_isPullbackSquare` exhibits the pullback of `Dom.sharp f`
and `Dom.sharpTotal q` as a `Dom.IsPullbackSquare`.
`Dom.exists_total_lift_iff_rangeLiftPullback_section` specializes
`Dom.exists_total_lift_iff_exists_section` to this pullback.

The universal property is stated directly; no Mathlib limit instance is
declared. The present hypotheses do not imply the existence of a terminal
object, so the "hence all finite limits" consequence of Cor. 2.4.10 is not
bundled as a Lean result.

Thm. 2.3.2 is formalized in `PCats.DomTotalEmbedding`.
`RestrictionCategory.TotalSubcategory C` is the wide subcategory of total
morphisms, Rosolini's `C_T`, with binary products carried by the near product.
`Dom.totalEmbedding` sends an object to `Dom.total` of it and a total morphism
to the `Dom.Hom` with the same underlying morphism; it is full
(`Dom.totalEmbedding_full`) and faithful (`Dom.totalEmbedding_faithful`), with
the preimage written down rather than chosen. It preserves binary products:
`Dom.totalEmbedding_binaryProduct_existsUnique` is the direct universal
property against an arbitrary apex `A : Dom C`, not merely against apices in
the image.

Still unformalized as well are the `Pfn` remark; the classical recursion
category `T`; and a model of `PRecursionCategory`.
-/

@[expose] public section
