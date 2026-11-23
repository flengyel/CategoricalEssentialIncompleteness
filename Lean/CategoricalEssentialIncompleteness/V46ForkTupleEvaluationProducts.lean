/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkTupleEvaluation
public import CategoricalEssentialIncompleteness.V46ForkDerivationCoordinates
public import CategoricalEssentialIncompleteness.V46FullRestrictionProducts
public import CategoricalEssentialIncompleteness.V46TuringRestrictionEquivalence

/-! # Restriction products of partial tuple spans

The product object is the product in the total tuple category. Its projections
and partial pairing are the corresponding numerical operations under coding.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.ForkTupleEvaluation

def codedTupleProducts : RestrictionProducts.ProductData EnumerableCarriers.Carrier where
  prod := EnumerableCarriers.product
  fst := EnumerableCarriers.partialFst
  snd := EnumerableCarriers.partialSnd
  pair := EnumerableCarriers.partialPair
  fst_total := EnumerableCarriers.partialFst_total
  snd_total := EnumerableCarriers.partialSnd_total
  pair_fst := EnumerableCarriers.partialPair_fst
  pair_snd := EnumerableCarriers.partialPair_snd
  pair_restriction := EnumerableCarriers.rst_partialPair
  pair_proj := EnumerableCarriers.partialPair_proj

def codedForkProducts : RestrictionProducts.ProductData EffectiveFork.Object where
  prod := EffectiveFork.product
  fst := EffectiveFork.first
  snd := EffectiveFork.second
  pair := EffectiveFork.partialPair
  fst_total X Y := (ForkDerivation.codedFst ⟨X⟩ ⟨Y⟩).property
  snd_total X Y := (ForkDerivation.codedSnd ⟨X⟩ ⟨Y⟩).property
  pair_fst f g := EffectiveFork.Hom.ext (EnumerableCarriers.partialPair_fst f.center g.center)
    (EnumerableCarriers.partialPair_fst f.left g.left) (EnumerableCarriers.partialPair_fst f.right g.right)
  pair_snd f g := EffectiveFork.Hom.ext (EnumerableCarriers.partialPair_snd f.center g.center)
    (EnumerableCarriers.partialPair_snd f.left g.left) (EnumerableCarriers.partialPair_snd f.right g.right)
  pair_restriction f g := EffectiveFork.Hom.ext (EnumerableCarriers.rst_partialPair f.center g.center)
    (EnumerableCarriers.rst_partialPair f.left g.left) (EnumerableCarriers.rst_partialPair f.right g.right)
  pair_proj f := EffectiveFork.Hom.ext (EnumerableCarriers.partialPair_proj f.center)
    (EnumerableCarriers.partialPair_proj f.left) (EnumerableCarriers.partialPair_proj f.right)

def forkProduct (X Y : ForkSpans) : ForkSpans := ⟨X.obj ⨯ Y.obj⟩
def tupleProduct (X Y : TupleSpans) : TupleSpans := ⟨X.obj ⨯ Y.obj⟩

def forkProductIso (X Y : ForkSpans) :
    forkCode.obj (forkProduct X Y) ≅ codedForkProducts.prod (forkCode.obj X) (forkCode.obj Y) :=
  (PreservesRestriction.totalInclusion EffectiveFork.Object).mapIso
    (asIso (prodComparison NumericalForkPartialMaps.totalEquivalence.functor X.obj Y.obj) ≪≫
      ForkDerivation.productComparison _ _)

def tupleProductIso (X Y : TupleSpans) :
    tupleCode.obj (tupleProduct X Y) ≅ codedTupleProducts.prod (tupleCode.obj X) (tupleCode.obj Y) :=
  (PreservesRestriction.totalInclusion EnumerableCarriers.Carrier).mapIso
    (asIso (prodComparison NumericalTuples.comparison X.obj Y.obj) ≪≫
      (prodIsProd _ _).conePointUniqueUpToIso (EnumerableCarriers.productIsLimit _ _))

def forkProducts : RestrictionProducts.ProductData ForkSpans :=
  FullRestrictionProducts.restrictionProducts forkCode forkCode_restriction
    codedForkProducts forkProduct forkProductIso

def tupleProducts : RestrictionProducts.ProductData TupleSpans :=
  FullRestrictionProducts.restrictionProducts tupleCode tupleCode_restriction
    codedTupleProducts tupleProduct tupleProductIso

theorem fork_product_map {W X Y Z : ForkSpans} (f : W ⟶ X) (g : Y ⟶ Z) :
    forkCode.map (forkProducts.map f g) ≫ (forkProductIso X Z).hom =
      (forkProductIso W Y).hom ≫ EffectiveFork.productMap (forkCode.map f) (forkCode.map g) :=
  FullRestrictionProducts.map_comparison _ _ _ _ _ _ _

theorem tuple_product_map {W X Y Z : TupleSpans} (f : W ⟶ X) (g : Y ⟶ Z) :
    tupleCode.map (tupleProducts.map f g) ≫ (tupleProductIso X Z).hom =
      (tupleProductIso W Y).hom ≫ EnumerableCarriers.partialProdMap (tupleCode.map f) (tupleCode.map g) :=
  FullRestrictionProducts.map_comparison _ _ _ _ _ _ _

theorem forkCode_total {X Y : ForkSpans} (f : X.obj ⟶ Y.obj) :
    forkCode.map (PartialMaps.ofTotal f) = (NumericalForkPartialMaps.totalEquivalence.functor.map f).hom := by
  change PartialSpans.inverse (NumericalForkPartialMaps.totalEquivalence.functor.map (𝟙 X.obj)) ≫
    (NumericalForkPartialMaps.totalEquivalence.functor.map f).hom = _
  have h := PartialSpans.hom_inverse (NumericalForkPartialMaps.totalEquivalence.functor.map (𝟙 X.obj))
  have hi : (NumericalForkPartialMaps.totalEquivalence.functor.map (𝟙 X.obj)).hom = 𝟙 _ :=
    congrArg (fun k => k.hom) (NumericalForkPartialMaps.totalEquivalence.functor.map_id X.obj)
  rw [hi, Category.id_comp] at h
  rw [h, Category.id_comp]

theorem tupleCode_total {X Y : TupleSpans} (f : X.obj ⟶ Y.obj) :
    tupleCode.map (PartialMaps.ofTotal f) = (NumericalTuples.comparison.map f).hom := by
  change PartialSpans.inverse (NumericalTuples.comparison.map (𝟙 X.obj)) ≫ (NumericalTuples.comparison.map f).hom = _
  have h := PartialSpans.hom_inverse (NumericalTuples.comparison.map (𝟙 X.obj))
  have hi : (NumericalTuples.comparison.map (𝟙 X.obj)).hom = 𝟙 _ :=
    congrArg (fun k => k.hom) (NumericalTuples.comparison.map_id X.obj)
  rw [hi, Category.id_comp] at h
  rw [h, Category.id_comp]

theorem codedFork_turing :
    @RecursionCategory.IsTuringMorphism _ _ codedForkProducts.pcategoryStruct
      codedForkProducts.pcategoryLaws EffectiveFork.V EffectiveFork.V EffectiveFork.V EffectiveFork.tau := by
  intro X f
  refine ⟨EffectiveFork.parameter f, ?_, EffectiveFork.tau_parameterization f⟩
  change @PCategoryStruct.rst _ _ codedForkProducts.pcategoryStruct _ _ _ = _
  rw [codedForkProducts.restriction_eq]
  exact EffectiveFork.parameter_total f

theorem codedEndpoint_turing :
    @RecursionCategory.IsTuringMorphism _ _ codedTupleProducts.pcategoryStruct
      codedTupleProducts.pcategoryLaws EffectiveFork.natCarrier EffectiveFork.natCarrier
      EffectiveFork.natCarrier EffectiveFork.endpointEvaluator := by
  intro X f
  refine ⟨EffectiveFork.endpointEncoding (EffectiveFork.specialize (EffectiveFork.program f))
    (EffectiveFork.specialize_computable _), ?_, EffectiveFork.endpoint_parameterization f⟩
  change @PCategoryStruct.rst _ _ codedTupleProducts.pcategoryStruct _ _ _ = _
  rw [codedTupleProducts.restriction_eq]
  exact EnumerableCarriers.totalFromFunction_total _ _ _

end CategoricalEssentialIncompleteness.V46.ForkTupleEvaluation
