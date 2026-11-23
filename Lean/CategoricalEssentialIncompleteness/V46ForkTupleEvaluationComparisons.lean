/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkTupleEvaluationProducts

/-! # Restriction products under evaluation of tuple spans -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkTupleEvaluation

abbrev baseEval (j : WalkingSpan) := (CategoryTheory.evaluation WalkingSpan NumericalTuples.Object).obj j

def productComparison (j : WalkingSpan) (X Y : ForkSpans) :
    (evaluation j).obj (forkProduct X Y) ≅ tupleProduct ((evaluation j).obj X) ((evaluation j).obj Y) :=
  PartialMaps.totalEmbedding.mapIso (asIso (prodComparison (baseEval j) X.obj Y.obj))

theorem fork_first (X Y : ForkSpans) : forkProducts.fst X Y = PartialMaps.ofTotal prod.fst := by
  apply forkCode.map_injective
  rw [forkCode_total]
  change forkCode.map (FullRestrictionProducts.first _ _ _ _ X Y) = _
  rw [FullRestrictionProducts.first_value]
  let F := NumericalForkPartialMaps.totalEquivalence.functor
  have h : (prodComparison F X.obj Y.obj ≫ (ForkDerivation.productComparison (F.obj X.obj) (F.obj Y.obj)).hom) ≫
      ForkDerivation.codedFst _ _ = F.map prod.fst := by
    rw [Category.assoc, ForkDerivation.productComparison_fst, prodComparison_fst]
  exact congrArg (fun k : F.obj (X.obj ⨯ Y.obj) ⟶ F.obj X.obj => k.hom) h

theorem fork_second (X Y : ForkSpans) : forkProducts.snd X Y = PartialMaps.ofTotal prod.snd := by
  apply forkCode.map_injective
  rw [forkCode_total]
  change forkCode.map (FullRestrictionProducts.second _ _ _ _ X Y) = _
  rw [FullRestrictionProducts.second_value]
  let F := NumericalForkPartialMaps.totalEquivalence.functor
  have h : (prodComparison F X.obj Y.obj ≫ (ForkDerivation.productComparison (F.obj X.obj) (F.obj Y.obj)).hom) ≫
      ForkDerivation.codedSnd _ _ = F.map prod.snd := by
    rw [Category.assoc, ForkDerivation.productComparison_snd, prodComparison_snd]
  exact congrArg (fun k : F.obj (X.obj ⨯ Y.obj) ⟶ F.obj Y.obj => k.hom) h

def numericProduct (X Y : EnumerableCarriers.Total) : X ⨯ Y ≅ EnumerableCarriers.totalProduct X Y :=
  (prodIsProd X Y).conePointUniqueUpToIso (EnumerableCarriers.productIsLimit X Y)

theorem numericProduct_fst (X Y : EnumerableCarriers.Total) :
    (numericProduct X Y).hom ≫ EnumerableCarriers.totalFst X Y = prod.fst :=
  IsLimit.conePointUniqueUpToIso_hom_comp (prodIsProd X Y) (EnumerableCarriers.productIsLimit X Y) ⟨.left⟩

theorem numericProduct_snd (X Y : EnumerableCarriers.Total) :
    (numericProduct X Y).hom ≫ EnumerableCarriers.totalSnd X Y = prod.snd :=
  IsLimit.conePointUniqueUpToIso_hom_comp (prodIsProd X Y) (EnumerableCarriers.productIsLimit X Y) ⟨.right⟩

theorem tuple_first (X Y : TupleSpans) : tupleProducts.fst X Y = PartialMaps.ofTotal prod.fst := by
  apply tupleCode.map_injective
  rw [tupleCode_total]
  change tupleCode.map (FullRestrictionProducts.first _ _ _ _ X Y) = _
  rw [FullRestrictionProducts.first_value]
  let F := NumericalTuples.comparison
  have h : (prodComparison F X.obj Y.obj ≫ (numericProduct (F.obj X.obj) (F.obj Y.obj)).hom) ≫
      EnumerableCarriers.totalFst _ _ = F.map prod.fst := by
    rw [Category.assoc, numericProduct_fst, prodComparison_fst]
  exact congrArg (fun k : F.obj (X.obj ⨯ Y.obj) ⟶ F.obj X.obj => k.hom) h

theorem tuple_second (X Y : TupleSpans) : tupleProducts.snd X Y = PartialMaps.ofTotal prod.snd := by
  apply tupleCode.map_injective
  rw [tupleCode_total]
  change tupleCode.map (FullRestrictionProducts.second _ _ _ _ X Y) = _
  rw [FullRestrictionProducts.second_value]
  let F := NumericalTuples.comparison
  have h : (prodComparison F X.obj Y.obj ≫ (numericProduct (F.obj X.obj) (F.obj Y.obj)).hom) ≫
      EnumerableCarriers.totalSnd _ _ = F.map prod.snd := by
    rw [Category.assoc, numericProduct_snd, prodComparison_snd]
  exact congrArg (fun k : F.obj (X.obj ⨯ Y.obj) ⟶ F.obj Y.obj => k.hom) h

@[reassoc] theorem comparison_fst (j : WalkingSpan) (X Y : ForkSpans) :
    (productComparison j X Y).hom ≫ tupleProducts.fst _ _ = (evaluation j).map (forkProducts.fst X Y) := by
  rw [tuple_first, fork_first, PartialMaps.inducedFunctor_ofTotal]
  change PartialMaps.ofTotal _ ≫ PartialMaps.ofTotal _ = _
  rw [← PartialMaps.ofTotal_comp]
  exact congrArg PartialMaps.ofTotal (prodComparison_fst (baseEval j) X.obj Y.obj)

@[reassoc] theorem comparison_snd (j : WalkingSpan) (X Y : ForkSpans) :
    (productComparison j X Y).hom ≫ tupleProducts.snd _ _ = (evaluation j).map (forkProducts.snd X Y) := by
  rw [tuple_second, fork_second, PartialMaps.inducedFunctor_ofTotal]
  change PartialMaps.ofTotal _ ≫ PartialMaps.ofTotal _ = _
  rw [← PartialMaps.ofTotal_comp]
  exact congrArg PartialMaps.ofTotal (prodComparison_snd (baseEval j) X.obj Y.obj)

theorem evaluation_pair (j : WalkingSpan) {W X Y : ForkSpans} (f : W ⟶ X) (g : W ⟶ Y) :
    (evaluation j).map (forkProducts.pair f g) ≫ (productComparison j X Y).hom =
      tupleProducts.pair ((evaluation j).map f) ((evaluation j).map g) := by
  apply tupleProducts.hom_ext
  · rw [Category.assoc, comparison_fst, ← (evaluation j).map_comp, forkProducts.pair_fst,
      (evaluation j).map_comp, evaluation_restriction j g, tupleProducts.pair_fst]
  · rw [Category.assoc, comparison_snd, ← (evaluation j).map_comp, forkProducts.pair_snd,
      (evaluation j).map_comp, evaluation_restriction j f, tupleProducts.pair_snd]

theorem evaluation_product (j : WalkingSpan) {W X Y Z : ForkSpans} (f : W ⟶ X) (g : Y ⟶ Z) :
    (evaluation j).map (forkProducts.map f g) ≫ (productComparison j X Z).hom =
      (productComparison j W Y).hom ≫ tupleProducts.map ((evaluation j).map f) ((evaluation j).map g) := by
  unfold RestrictionProducts.ProductData.map
  rw [evaluation_pair, tupleProducts.comp_pair, (evaluation j).map_comp, (evaluation j).map_comp,
    comparison_fst_assoc, comparison_snd_assoc]

def componentProductIso (j : WalkingSpan) (X Y : ForkSpans) :
    tupleCode.obj ((evaluation j).obj (forkProduct X Y)) ≅
      codedTupleProducts.prod (tupleCode.obj ((evaluation j).obj X)) (tupleCode.obj ((evaluation j).obj Y)) := by
  rcases j with _ | (_ | _)
  exacts [(EffectiveFork.evaluation .center).mapIso (forkProductIso X Y),
    (EffectiveFork.evaluation .left).mapIso (forkProductIso X Y),
    (EffectiveFork.evaluation .right).mapIso (forkProductIso X Y)]

theorem component_product_comparison (j : WalkingSpan) (X Y : ForkSpans) :
    tupleCode.map (productComparison j X Y).hom ≫ (tupleProductIso _ _).hom =
      (componentProductIso j X Y).hom := by
  have hf := FullRestrictionProducts.first_value forkCode codedForkProducts forkProduct forkProductIso X Y
  have hs := FullRestrictionProducts.second_value forkCode codedForkProducts forkProduct forkProductIso X Y
  apply codedTupleProducts.hom_ext
  · rw [Category.assoc, ← FullRestrictionProducts.first_value tupleCode codedTupleProducts
      tupleProduct tupleProductIso, ← tupleCode.map_comp]
    change tupleCode.map ((productComparison j X Y).hom ≫ tupleProducts.fst _ _) = _
    rw [comparison_fst, evaluation_value]
    rcases j with _ | (_ | _)
    exacts [congrArg (fun k => k.center) hf, congrArg (fun k => k.left) hf, congrArg (fun k => k.right) hf]
  · rw [Category.assoc, ← FullRestrictionProducts.second_value tupleCode codedTupleProducts
      tupleProduct tupleProductIso, ← tupleCode.map_comp]
    change tupleCode.map ((productComparison j X Y).hom ≫ tupleProducts.snd _ _) = _
    rw [comparison_snd, evaluation_value]
    rcases j with _ | (_ | _)
    exacts [congrArg (fun k => k.center) hs, congrArg (fun k => k.left) hs, congrArg (fun k => k.right) hs]

end CategoricalEssentialIncompleteness.V46.ForkTupleEvaluation
