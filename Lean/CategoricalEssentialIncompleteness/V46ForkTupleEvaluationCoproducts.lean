/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkTupleEvaluationComparisons
public import CategoricalEssentialIncompleteness.V46ForkSignedAtomInclusion

/-! # Finite joins and binary coproducts under evaluation of tuple spans -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkTupleEvaluation

instance : RestrictionZero ForkSpans where
  restrict_zero X Y := by
    apply forkCode.map_injective
    rw [forkCode_restriction]
    change rst (forkCode.map (forkCode.preimage 0)) = forkCode.map (forkCode.preimage 0)
    rw [forkCode.map_preimage, forkCode.map_preimage, RestrictionZero.restrict_zero]

instance : RestrictionZero TupleSpans where
  restrict_zero X Y := by
    apply tupleCode.map_injective
    rw [tupleCode_restriction]
    change rst (tupleCode.map (tupleCode.preimage 0)) = tupleCode.map (tupleCode.preimage 0)
    rw [tupleCode.map_preimage, tupleCode.map_preimage, RestrictionZero.restrict_zero]

theorem evaluation_bot (j : WalkingSpan) (X : ForkSpans) :
    evaluatedIdem j (⊥ : Idem X) = ⊥ := Idem.ext (evaluation_zero j X X)

theorem evaluation_finset {ι : Type*} {X : ForkSpans} (j : WalkingSpan) (s : Finset ι)
    (a : ι → Idem X) : evaluatedIdem j (s.sup a) = s.sup (fun i => evaluatedIdem j (a i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using evaluation_bot j X
  | @insert i s hi ih => simp only [Finset.sup_insert, evaluation_sup, ih]

universe u v u' v'
section
variable {A : Type u} {B : Type u'} [Category.{v} A] [Category.{v'} B]
variable [CoprodStruct B] [CategoryTheory.HasCoproducts B] (F : A ⥤ B) [F.Full] [F.Faithful]

def sumColimit {X Y Z : A} (l : X ⟶ Z) (r : Y ⟶ Z) (i : coprod (F.obj X) (F.obj Y) ≅ F.obj Z)
    (hl : i0 (F.obj X) (F.obj Y) ≫ i.hom = F.map l)
    (hr : i1 (F.obj X) (F.obj Y) ≫ i.hom = F.map r) : IsColimit (BinaryCofan.mk l r) :=
  BinaryCofan.isColimitMk (fun s => F.preimage (i.inv ≫ copair (F.map s.inl) (F.map s.inr)))
    (by intro s; apply F.map_injective; rw [F.map_comp, F.map_preimage, ← hl]; simp [i0_copair])
    (by intro s; apply F.map_injective; rw [F.map_comp, F.map_preimage, ← hr]; simp [i1_copair]) (by
      intro s m h₁ h₂
      apply F.map_injective
      rw [F.map_preimage]
      apply (cancel_epi i.hom).mp
      rw [i.hom_inv_id_assoc]
      apply CategoryTheory.HasCoproducts.hom_ext
      · rw [← Category.assoc, hl, ← F.map_comp, h₁, i0_copair]
      · rw [← Category.assoc, hr, ← F.map_comp, h₂, i1_copair])
end

def forkSum (X Y : ForkSpans) : ForkSpans := ⟨X.obj ⨿ Y.obj⟩
def tupleSum (X Y : TupleSpans) : TupleSpans := ⟨X.obj ⨿ Y.obj⟩

def forkSumIso (X Y : ForkSpans) : coprod (forkCode.obj X) (forkCode.obj Y) ≅ forkCode.obj (forkSum X Y) :=
  (PreservesRestriction.totalInclusion EffectiveFork.Object).mapIso
    (ForkDerivation.sumComparison _ _ ≪≫
      asIso (coprodComparison NumericalForkPartialMaps.totalEquivalence.functor X.obj Y.obj))

def forkSumColimit (X Y : ForkSpans) :
    IsColimit (BinaryCofan.mk (PartialMaps.ofTotal coprod.inl : X ⟶ forkSum X Y)
      (PartialMaps.ofTotal coprod.inr : Y ⟶ forkSum X Y)) := by
  let F := NumericalForkPartialMaps.totalEquivalence.functor
  apply sumColimit forkCode _ _ (forkSumIso X Y)
  · rw [forkCode_total]
    have h : ForkDerivation.codedInl (F.obj X.obj) (F.obj Y.obj) ≫
        (ForkDerivation.sumComparison _ _).hom ≫ coprodComparison F X.obj Y.obj = F.map coprod.inl := by
      rw [← Category.assoc, ForkDerivation.codedInl_comparison, coprodComparison_inl]
    exact congrArg (fun k => k.hom) h
  · rw [forkCode_total]
    have h : ForkDerivation.codedInr (F.obj X.obj) (F.obj Y.obj) ≫
        (ForkDerivation.sumComparison _ _).hom ≫ coprodComparison F X.obj Y.obj = F.map coprod.inr := by
      rw [← Category.assoc, ForkDerivation.codedInr_comparison, coprodComparison_inr]
    exact congrArg (fun k => k.hom) h

def numericSum (X Y : EnumerableCarriers.Total) : EnumerableCarriers.totalCoproduct X Y ≅ X ⨿ Y :=
  (EnumerableCarriers.coproductIsColimit X Y).coconePointUniqueUpToIso (colimit.isColimit (Limits.pair X Y))

theorem numericSum_inl (X Y : EnumerableCarriers.Total) :
    EnumerableCarriers.totalInl X Y ≫ (numericSum X Y).hom = coprod.inl :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (EnumerableCarriers.coproductIsColimit X Y)
    (colimit.isColimit (Limits.pair X Y)) ⟨.left⟩

theorem numericSum_inr (X Y : EnumerableCarriers.Total) :
    EnumerableCarriers.totalInr X Y ≫ (numericSum X Y).hom = coprod.inr :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (EnumerableCarriers.coproductIsColimit X Y)
    (colimit.isColimit (Limits.pair X Y)) ⟨.right⟩

def tupleSumIso (X Y : TupleSpans) : coprod (tupleCode.obj X) (tupleCode.obj Y) ≅ tupleCode.obj (tupleSum X Y) :=
  (PreservesRestriction.totalInclusion EnumerableCarriers.Carrier).mapIso
    (numericSum _ _ ≪≫ asIso (coprodComparison NumericalTuples.comparison X.obj Y.obj))

def tupleSumColimit (X Y : TupleSpans) :
    IsColimit (BinaryCofan.mk (PartialMaps.ofTotal coprod.inl : X ⟶ tupleSum X Y)
      (PartialMaps.ofTotal coprod.inr : Y ⟶ tupleSum X Y)) := by
  let F := NumericalTuples.comparison
  apply sumColimit tupleCode _ _ (tupleSumIso X Y)
  · rw [tupleCode_total]
    have h : EnumerableCarriers.totalInl (F.obj X.obj) (F.obj Y.obj) ≫
        (numericSum _ _).hom ≫ coprodComparison F X.obj Y.obj = F.map coprod.inl := by
      rw [← Category.assoc, numericSum_inl, coprodComparison_inl]
    exact congrArg (fun k => k.hom) h
  · rw [tupleCode_total]
    have h : EnumerableCarriers.totalInr (F.obj X.obj) (F.obj Y.obj) ≫
        (numericSum _ _).hom ≫ coprodComparison F X.obj Y.obj = F.map coprod.inr := by
      rw [← Category.assoc, numericSum_inr, coprodComparison_inr]
    exact congrArg (fun k => k.hom) h

def sumComparison (j : WalkingSpan) (X Y : ForkSpans) :
    tupleSum ((evaluation j).obj X) ((evaluation j).obj Y) ≅ (evaluation j).obj (forkSum X Y) :=
  PartialMaps.totalEmbedding.mapIso (asIso (coprodComparison (baseEval j) X.obj Y.obj))

theorem comparison_inl (j : WalkingSpan) (X Y : ForkSpans) :
    PartialMaps.ofTotal coprod.inl ≫ (sumComparison j X Y).hom =
      (evaluation j).map (PartialMaps.ofTotal coprod.inl : X ⟶ forkSum X Y) := by
  rw [PartialMaps.inducedFunctor_ofTotal]
  change PartialMaps.ofTotal _ ≫ PartialMaps.ofTotal _ = _
  rw [← PartialMaps.ofTotal_comp]
  exact congrArg PartialMaps.ofTotal (coprodComparison_inl (baseEval j) (A := X.obj) (B := Y.obj))

theorem comparison_inr (j : WalkingSpan) (X Y : ForkSpans) :
    PartialMaps.ofTotal coprod.inr ≫ (sumComparison j X Y).hom =
      (evaluation j).map (PartialMaps.ofTotal coprod.inr : Y ⟶ forkSum X Y) := by
  rw [PartialMaps.inducedFunctor_ofTotal]
  change PartialMaps.ofTotal _ ≫ PartialMaps.ofTotal _ = _
  rw [← PartialMaps.ofTotal_comp]
  exact congrArg PartialMaps.ofTotal (coprodComparison_inr (baseEval j) (A := X.obj) (B := Y.obj))

def evaluatedSumColimit (j : WalkingSpan) (X Y : ForkSpans) :
    IsColimit (BinaryCofan.mk ((evaluation j).map (PartialMaps.ofTotal coprod.inl : X ⟶ forkSum X Y))
      ((evaluation j).map (PartialMaps.ofTotal coprod.inr : Y ⟶ forkSum X Y))) :=
  (tupleSumColimit _ _).ofIsoColimit (BinaryCofan.ext (sumComparison j X Y)
    (comparison_inl j X Y) (comparison_inr j X Y))

end CategoricalEssentialIncompleteness.V46.ForkTupleEvaluation
