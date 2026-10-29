import PCats

/-!
Axiom check. Run with `lake env lean check_axioms.lean`.

`lake build` reports only that the files elaborate. Lean does not propagate the
`sorry` marker across declarations, so a lemma resting on a sorried instance
compiles without a warning. `#print axioms` follows the transitive dependency
and is the check that matters.

A clean result lists only `propext` and `Quot.sound`. `Quot.sound` enters
through `funext`, so it appears both in the concrete `OptionKleisli` model and
in the abstract countable-coproduct universal property, whose uniqueness clause
compares families rather than morphisms. `Classical.choice` should appear
nowhere: the development is constructive.

Elimination of `Nonempty (W ≅ V)` occurs inside a proposition and does not
introduce `Classical.choice`.

`#print axioms` on a name that does not exist is an error, so this file also
serves as a check that every module is present and up to date.

The roots below are chosen to cover the file by dependency: everything proved
from R1–R4 occurs among the transitive dependencies of `inducedRestriction`,
the domain calculus among those of `rst_nearProd_map`, and so on. A
declaration that is not a transitive dependency of any root is untested
here.
-/

open CategoryTheory

-- Restriction categories and the induced instance (R1–R4 and all downstream).
#print axioms PCategory.inducedRestriction
#print axioms PCategory.rst_eq
#print axioms PCategory.rst_partialPairing_eq

-- Heller's projection-generated subcategory and the naturalizer containments.
#print axioms PCategory.projectionGenerated
#print axioms PCategory.projectionGenerated_p0
#print axioms PCategory.projectionGenerated_p1
#print axioms PCategory.projectionGenerated_nearProd_map
#print axioms PCategory.instIsMultiplicativeProjectionGenerated
#print axioms PCategory.ProjectionSubcategory
#print axioms PCategory.projectionGenerated_le
#print axioms PCategory.projectionGenerated_isTotal
#print axioms PCategory.p0_nat_of_projectionGenerated
#print axioms PCategory.p1_nat_of_projectionGenerated

-- Domain calculus and Lemma A.3.
#print axioms PCategory.nearProd_domain_left
#print axioms PCategory.nearProd_domain_right
#print axioms PCategory.comp_p0_domain_of_comp_rst
#print axioms PCategory.comp_p1_domain_of_comp_rst
#print axioms PCategory.rst_nearProd_map
#print axioms PCategory.p0_proj_domain_id
#print axioms PCategory.p1_proj_domain_id
#print axioms PCategory.p0_nat_of_isTotal
#print axioms PCategory.p1_nat_of_isTotal

-- The near product as a product on the total subcategory.
#print axioms PCategory.existsUnique_partialPairing

-- Invertibility of the associator and the symmetry, derived not assumed.
#print axioms PCategory.isIso_assoc
#print axioms PCategory.isIso_swap

-- The erratum.
#print axioms Erratum.assoc_diag_nearProd_id
#print axioms Erratum.coassoc
#print axioms Erratum.diag_nearProd_p1_absorb
#print axioms Erratum.id_nearProd_p1_absorb
#print axioms Erratum.nearProd_p1_factor
#print axioms Erratum.assoc_nearProd_right

-- Dom(X): the order and the meet.
#print axioms DomSemilattice.instPartialOrder
#print axioms DomSemilattice.le_meet
#print axioms DomSemilattice.rst_zero
#print axioms DomSemilattice.bot_le
#print axioms DomSemilattice.IsUnion.le_of_forall_le
#print axioms DomSemilattice.IsUnion.unique
#print axioms DomSemilattice.comm_comp
#print axioms DomSemilattice.rightTimes
#print axioms HasRanges.ran_comp_of_section

-- Ranges, sections, choice, total range lifting.
#print axioms IsRange.unique
#print axioms HasRanges.ran_id
#print axioms exists_isRange_of_hasChoice
#print axioms hasTotalRangeLifting_of_hasChoice
#print axioms hasWeakChoice_of_hasChoice

-- Coproducts: the nested identities are theorems here, and the coproduct is a
-- coproduct with no totality hypothesis.
#print axioms HasCoproducts.i0_i0
#print axioms HasCoproducts.i1_i1
#print axioms HasCoproducts.copair_inj
#print axioms HasCoproducts.existsUnique_copair
#print axioms HasCoproducts.copair_comp
#print axioms HasCoproducts.rst_copair
#print axioms HasCoproducts.rst_coprod_map_self
#print axioms HasNCoproducts.ninj_ncopair
#print axioms HasNCoproducts.ncopair_ninj
#print axioms HasNCoproducts.eq_ncopair_of_ninj
#print axioms HasNCoproducts.existsUnique_ncopair
#print axioms HasNCoproducts.ncopair_comp
#print axioms HasNCoproducts.rst_ncopair
#print axioms HasNCoproducts.isTotal_ncopair
#print axioms CountablyDistributive.undistribL_distribL
#print axioms CountablyDistributive.distribL_undistribL
#print axioms CountablyDistributive.undistribR_distribR
#print axioms CountablyDistributive.distribR_undistribR
#print axioms CountablyDistributive.undistribL_nat
#print axioms CountablyDistributive.undistribR_nat
#print axioms CountablyDistributive.distribL_nat
#print axioms CountablyDistributive.distribR_nat
#print axioms CountablyDistributive.nearProd_id_ncopair
#print axioms CountablyDistributive.nearProd_ncopair_id
#print axioms HasRanges.ran_ncopair_isUnion
#print axioms HasRanges.ran_ncopair_isStableUnion

-- Dom(C) and Lemma A.4.
#print axioms Dom.instCategory
#print axioms Dom.sharpOfTotalLift_comp_sharp
#print axioms Dom.exists_total_lift_iff_exists_section

-- Binary products in Dom(C), the binary-product clause of Rosolini Thm. 2.3.3.
#print axioms Dom.binaryProduct
#print axioms Dom.binaryProductFst
#print axioms Dom.binaryProductSnd
#print axioms Dom.binaryProductLift
#print axioms Dom.binaryProduct_existsUnique

-- Inverse images of subdomains, the inverse-image clause of Thm. 2.3.3.
#print axioms Dom.Subdomain.toDom
#print axioms Dom.Subdomain.inclusion
#print axioms Dom.Subdomain.inclusion_mono
#print axioms Dom.Subdomain.compose
#print axioms Dom.Subdomain.compose_inclusion
#print axioms Dom.Subdomain.inverseImage
#print axioms Dom.Subdomain.inverseImageMap
#print axioms Dom.Subdomain.inverseImage_comm
#print axioms Dom.Subdomain.inverseImageLift
#print axioms Dom.Subdomain.inverseImage_existsUnique

-- The comparison isomorphism with an inverse image along an isomorphism.
#print axioms Dom.Subdomain.inverseImageIso
#print axioms Dom.Subdomain.inverseImageIso_hom_hom
#print axioms Dom.Subdomain.inverseImageIso_inv_hom
#print axioms Dom.Subdomain.inverseImageIso_hom_inclusion

-- The morphisms isomorphic over a fixed codomain to a canonical inclusion.
#print axioms Dom.Subdomain.top
#print axioms Dom.subdomainMorphisms
#print axioms Dom.subdomainMorphisms_iff
#print axioms Dom.Subdomain.inclusion_mem_subdomainMorphisms
#print axioms Dom.id_mem_subdomainMorphisms
#print axioms Dom.mono_of_mem_subdomainMorphisms
#print axioms Dom.subdomainMorphisms_precomp_iso
#print axioms Dom.subdomainMorphisms_precomp_iso_iff
#print axioms Dom.subdomainMorphisms_comp
#print axioms Dom.instIsMultiplicativeSubdomainMorphisms
#print axioms Dom.exists_pullback_of_mem_subdomainMorphisms

-- Equalizers in Dom(C), the equalizer clause of Rosolini Cor. 2.4.10.
#print axioms Dom.binaryProductDiagonal
#print axioms Dom.binaryProductDiagonal_fst
#print axioms Dom.binaryProductDiagonal_snd
#print axioms Dom.diagonalSubdomain
#print axioms Dom.diagonalSubdomain_idem
#print axioms Dom.diagonalFactor
#print axioms Dom.diagonalFactor_hom
#print axioms Dom.diagonalFactor_inclusion
#print axioms Dom.diagonalFactorIso
#print axioms Dom.diagonalSubdomain_fst_eq_snd
#print axioms Dom.equalizerSubdomain
#print axioms Dom.equalizerObject
#print axioms Dom.equalizerInclusion
#print axioms Dom.equalizer_comm
#print axioms Dom.equalizerLift
#print axioms Dom.equalizerLift_inclusion
#print axioms Dom.equalizerLift_unique
#print axioms Dom.equalizer_existsUnique

-- Pullbacks of an arbitrary cospan, from binary products and equalizers.
#print axioms Dom.pullbackObject
#print axioms Dom.pullbackFst
#print axioms Dom.pullbackSnd
#print axioms Dom.pullback_comm
#print axioms Dom.pullbackLift
#print axioms Dom.pullbackLift_fst
#print axioms Dom.pullbackLift_snd
#print axioms Dom.pullbackLift_unique
#print axioms Dom.pullback_existsUnique
-- Lemma A.4 specialized to the explicit pullback.
#print axioms Dom.rangeLiftPullback_isPullbackSquare
#print axioms Dom.exists_total_lift_iff_rangeLiftPullback_section

-- Binary products in the total subcategory C_T.
#print axioms RestrictionCategory.TotalSubcategory
#print axioms RestrictionCategory.TotalSubcategory.binaryProduct
#print axioms RestrictionCategory.TotalSubcategory.binaryProduct_obj
#print axioms RestrictionCategory.TotalSubcategory.binaryProductFst
#print axioms RestrictionCategory.TotalSubcategory.binaryProductFst_hom
#print axioms RestrictionCategory.TotalSubcategory.binaryProductSnd
#print axioms RestrictionCategory.TotalSubcategory.binaryProductSnd_hom
#print axioms RestrictionCategory.TotalSubcategory.binaryProductLift
#print axioms RestrictionCategory.TotalSubcategory.binaryProductLift_hom
#print axioms RestrictionCategory.TotalSubcategory.binaryProductLift_fst
#print axioms RestrictionCategory.TotalSubcategory.binaryProductLift_snd
#print axioms RestrictionCategory.TotalSubcategory.binaryProductLift_unique
#print axioms RestrictionCategory.TotalSubcategory.binaryProduct_existsUnique

-- The total-object embedding, Rosolini Thm. 2.3.2.
#print axioms Dom.totalEmbedding
#print axioms Dom.totalEmbedding_obj
#print axioms Dom.totalEmbedding_map_hom
#print axioms Dom.totalEmbedding_full
#print axioms Dom.totalEmbedding_faithful
#print axioms Dom.totalEmbeddingFullyFaithful
#print axioms Dom.totalEmbeddingBinaryProductLift
#print axioms Dom.totalEmbeddingBinaryProductLift_hom
#print axioms Dom.totalEmbeddingBinaryProductLift_fst
#print axioms Dom.totalEmbeddingBinaryProductLift_snd
#print axioms Dom.totalEmbeddingBinaryProductLift_unique
#print axioms Dom.totalEmbedding_binaryProduct_existsUnique

-- The dominical axioms N1–N4 and the structures they yield.
#print axioms DiPaolaHeller.Dominical.toPCategory
#print axioms DiPaolaHeller.Dominical.toProdominical

-- Lemma 3.5(iii), the totality comparison, and Prop. A.5.
#print axioms DiPaolaHeller.Dominical.eq_zero_iff_rst_eq_zero
#print axioms DiPaolaHeller.Dominical.isTotal_iff_rst_eq_id
#print axioms DiPaolaHeller.Dominical.isTotal_iff_restrictionTotal
#print axioms DiPaolaHeller.Dominical.totalityImpliesRestrictionTotal
#print axioms DiPaolaHeller.Dominical.toPRecursionCategory

-- Di Paola–Heller totality and the conditional transport at A.6, 381–388.
#print axioms DiPaolaHeller.isTotal_id
#print axioms DiPaolaHeller.IsTotal.comp
#print axioms DiPaolaHeller.isTotal_hom
#print axioms DiPaolaHeller.isTotal_inv
#print axioms DiPaolaHeller.IsTuringMorphism.toRecursionCategory
#print axioms DiPaolaHeller.FixedSourceTuringData.toPRecursionCategory

-- The concrete model.
#print axioms OptionKleisli.instPCategoryStruct
#print axioms OptionKleisli.rst_apply
#print axioms OptionKleisli.isTotal_iff
#print axioms OptionKleisli.instCoprodStruct
#print axioms OptionKleisli.instHasCoproducts
#print axioms OptionKleisli.instDistributive
#print axioms OptionKleisli.instHasZeroMorphisms
#print axioms OptionKleisli.instProdominical
#print axioms OptionKleisli.instNCoprodStruct
#print axioms OptionKleisli.instHasNCoproducts
#print axioms OptionKleisli.instCountablyDistributive
