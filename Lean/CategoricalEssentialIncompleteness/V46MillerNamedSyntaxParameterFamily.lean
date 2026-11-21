/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxListTransport
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxFamilyTransport
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import Mathlib.CategoryTheory.Limits.Over

/-! # Finite-geometry constant-family squares for Over.post

The functor is not assumed to be an equivalence. No preservation of syntax
or list initiality is inferred. Only finite limits and coproducts are used
in these structural diagrams.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison.ParameterTransport
open ListTransport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteCoproducts F]
variable (R : C)

instance slice_preservesFiniteCoproducts : PreservesFiniteCoproducts (sliceFunctor F R) := by
  let : PreservesFiniteCoproducts (sliceFunctor F R ⋙ Over.forget (F.obj R)) := by
    change PreservesFiniteCoproducts (Over.forget R ⋙ F)
    infer_instance
  exact preservesFiniteCoproducts_of_reflects_of_preserves (sliceFunctor F R) (Over.forget (F.obj R))

/-- The slice functor compares constant families naturally in the coefficient or recursive
carrier, using the product comparison. -/
def familyNaturalIso :
    constantFamilyFunctor R ⋙ (sliceFunctor F R) ≅
      F ⋙ constantFamilyFunctor (F.obj R) := by
  refine NatIso.ofComponents (familyComparison F R) ?_
  intro X Y f
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · exact (Over.w _).trans (Over.w _).symm
  · change (F.map (prod.map (𝟙 R) f) ≫
        (familyComparison F R Y).hom.left) ≫ prod.snd =
      ((familyComparison F R X).hom.left ≫ prod.map (𝟙 (F.obj R)) (F.map f)) ≫ prod.snd
    simp only [Category.assoc, prod.map_snd]
    erw [familyComparison_snd, ← F.map_comp,
      prod.map_snd, F.map_comp]
    erw [← Category.assoc, familyComparison_snd]

omit [FinitaryExtensive C] [FinitaryExtensive D] [PreservesFiniteCoproducts F] in
/-- The terminal comparison square needs only terminal uniqueness;
it does not invert a constant-family comparison. -/
theorem family_unit :
    terminalComparison (sliceFunctor F R) ≫ constantUnitComparison (F.obj R) =
      (sliceFunctor F R).map (constantUnitComparison R) ≫
        (familyComparison F R (⊤_ C)).hom ≫
          (constantFamilyFunctor (F.obj R)).map (terminalComparison F) := by
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · exact (Over.w _).trans (Over.w _).symm
  · exact terminalIsTerminal.hom_ext _ _

omit [FinitaryExtensive C] [FinitaryExtensive D] [PreservesFiniteCoproducts F] in
/-- The product square follows from naturality of the universal product comparison. In
particular, it compares the parameter projections. -/
theorem family_product (X Y : C) :
    prodComparison (sliceFunctor F R)
        (constantFamily R X) (constantFamily R Y) ≫
      prod.map (familyComparison F R X).hom (familyComparison F R Y).hom ≫
        constantProductComparison (F.obj R) (F.obj X) (F.obj Y) =
      (sliceFunctor F R).map (constantProductComparison R X Y) ≫
        (familyComparison F R (X ⨯ Y)).hom ≫
          (constantFamilyFunctor (F.obj R)).map (prodComparison F X Y) := by
  apply (cancel_mono
    (prodComparison (constantFamilyFunctor (F.obj R)) (F.obj X) (F.obj Y))).mp
  simp only [Category.assoc,
    SyntaxParameterChange.constant_comparison_prodComparison, Category.comp_id]
  have hn := prodComparison_natural_of_natTrans (familyNaturalIso F R).hom
    (A := X) (B := Y)
  rw [prodComparison_comp, prodComparison_comp] at hn
  change (familyComparison F R (X ⨯ Y)).hom ≫
      ((constantFamilyFunctor (F.obj R)).map (prodComparison F X Y) ≫
        prodComparison (constantFamilyFunctor (F.obj R)) (F.obj X) (F.obj Y)) =
    ((sliceFunctor F R).map
        (prodComparison (constantFamilyFunctor R) X Y) ≫
      prodComparison (sliceFunctor F R)
        (constantFamily R X) (constantFamily R Y)) ≫
      prod.map (familyComparison F R X).hom (familyComparison F R Y).hom at hn
  rw [hn]
  simp only [Category.assoc]
  rw [← Category.assoc, ← Functor.map_comp,
    SyntaxParameterChange.constant_comparison_prodComparison,
    (sliceFunctor F R).map_id, Category.id_comp]

/-- Coproduct coherence uses preserved coproducts of the finite-geometry functor.
No inverse of the constant-family coproduct comparison is used. -/
theorem family_sum (X Y : C) :
    inv (coprodComparison (sliceFunctor F R)
      (constantFamily R X) (constantFamily R Y)) ≫
        coprod.map (familyComparison F R X).hom (familyComparison F R Y).hom ≫
          constantCoproductComparison (F.obj R) (F.obj X) (F.obj Y) =
      (sliceFunctor F R).map (constantCoproductComparison R X Y) ≫
        (familyComparison F R (X ⨿ Y)).hom ≫
          (constantFamilyFunctor (F.obj R)).map (inv (coprodComparison F X Y)) := by
  apply (cancel_epi (coprodComparison (sliceFunctor F R)
    (constantFamily R X) (constantFamily R Y))).mp
  rw [IsIso.hom_inv_id_assoc]
  apply coprod.hom_ext
  · simp only [coprod.inl_map_assoc, constantCoproductComparison,
      coprod.inl_desc, coprodComparison_inl_assoc]
    rw [← (sliceFunctor F R).map_comp_assoc, coprod.inl_desc]
    erw [(familyNaturalIso F R).hom.naturality_assoc (coprod.inl : X ⟶ X ⨿ Y)]
    simp only [Functor.comp_map, ← Functor.map_comp, map_inl_inv_coprodComparison]
    rfl
  · simp only [coprod.inr_map_assoc, constantCoproductComparison,
      coprod.inr_desc, coprodComparison_inr_assoc]
    rw [← (sliceFunctor F R).map_comp_assoc, coprod.inr_desc]
    erw [(familyNaturalIso F R).hom.naturality_assoc (coprod.inr : Y ⟶ X ⨿ Y)]
    simp only [Functor.comp_map, ← Functor.map_comp, map_inr_inv_coprodComparison]
    rfl

omit [FinitaryExtensive C] [FinitaryExtensive D] [PreservesFiniteCoproducts F] in
/-- Product coherence also allows arbitrary changes of the two
coefficient objects after applying the functor. -/
theorem family_product_map {X Y : C} {X' Y' : D}
    (u : F.obj X ⟶ X') (v : F.obj Y ⟶ Y') :
    prodComparison (sliceFunctor F R)
        (constantFamily R X) (constantFamily R Y) ≫
      prod.map ((familyComparison F R X).hom ≫ (constantFamilyFunctor (F.obj R)).map u)
        ((familyComparison F R Y).hom ≫ (constantFamilyFunctor (F.obj R)).map v) ≫
          constantProductComparison (F.obj R) X' Y' =
      (sliceFunctor F R).map (constantProductComparison R X Y) ≫
        (familyComparison F R (X ⨯ Y)).hom ≫
          (constantFamilyFunctor (F.obj R)).map (prodComparison F X Y ≫ prod.map u v) := by
  calc
    _ = (prodComparison (sliceFunctor F R)
        (constantFamily R X) (constantFamily R Y) ≫
        prod.map (familyComparison F R X).hom (familyComparison F R Y).hom ≫
        constantProductComparison (F.obj R) (F.obj X) (F.obj Y)) ≫
          (constantFamilyFunctor (F.obj R)).map (prod.map u v) := by
      rw [← prod.map_map]
      simp only [Category.assoc, constantProductComparison_natural]
    _ = _ := by
      rw [family_product, Functor.map_comp]
      simp only [Category.assoc]

/-- The corresponding coproduct square uses only functoriality and the
universal coproduct injections, including when a coefficient is initial. -/
theorem family_sum_map {X Y : C} {X' Y' : D}
    (u : F.obj X ⟶ X') (v : F.obj Y ⟶ Y') :
    inv (coprodComparison (sliceFunctor F R)
        (constantFamily R X) (constantFamily R Y)) ≫
      coprod.map ((familyComparison F R X).hom ≫ (constantFamilyFunctor (F.obj R)).map u)
        ((familyComparison F R Y).hom ≫ (constantFamilyFunctor (F.obj R)).map v) ≫
          constantCoproductComparison (F.obj R) X' Y' =
      (sliceFunctor F R).map (constantCoproductComparison R X Y) ≫
        (familyComparison F R (X ⨿ Y)).hom ≫
          (constantFamilyFunctor (F.obj R)).map
            (inv (coprodComparison F X Y) ≫ coprod.map u v) := by
  calc
    _ = (inv (coprodComparison (sliceFunctor F R)
        (constantFamily R X) (constantFamily R Y)) ≫
        coprod.map (familyComparison F R X).hom (familyComparison F R Y).hom ≫
        constantCoproductComparison (F.obj R) (F.obj X) (F.obj Y)) ≫
          (constantFamilyFunctor (F.obj R)).map (coprod.map u v) := by
      rw [← coprod.map_map]
      simp only [Category.assoc, constantCoproductComparison_natural]
    _ = _ := by
      rw [family_sum, Functor.map_comp]
      simp only [Category.assoc]

end CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison.ParameterTransport
