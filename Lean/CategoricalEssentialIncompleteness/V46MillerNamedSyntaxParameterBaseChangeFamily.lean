/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxParameterFamily

/-! # Finite-geometry family charts after an actual base isomorphism

Only the base-change functor is an equivalence. The original functor needs
its proved finite limits and coproducts, without any initiality assumption.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison.ParameterBaseChange
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteCoproducts F]
variable {R : C} {Q : D} (b : F.obj R ≅ Q)

abbrev functor : Over R ⥤ Over Q := Over.post F ⋙ Over.map b.hom

instance preservesFiniteLimits : PreservesFiniteLimits (functor F b) := by
  dsimp [functor]
  infer_instance

instance preservesFiniteCoproducts : PreservesFiniteCoproducts (functor F b) := by
  let : PreservesFiniteCoproducts (Over.post F (X := R)) :=
    ParameterTransport.slice_preservesFiniteCoproducts F R
  dsimp [functor]
  infer_instance

def familyComparison (X : C) :
    (functor F b).obj (constantFamily R X) ≅ constantFamily Q (F.obj X) :=
  Over.isoMk ((asIso (prodComparison F R X)) ≪≫ prod.mapIso b (Iso.refl _)) (by
    change (prodComparison F R X ≫ prod.map b.hom (𝟙 _)) ≫ prod.fst=F.map prod.fst ≫ b.hom
    simp [Category.assoc])

omit [FinitaryExtensive C] [FinitaryExtensive D] [PreservesFiniteCoproducts F] in
@[reassoc] theorem familyComparison_snd (X : C) :
    (familyComparison F b X).hom.left ≫ prod.snd=F.map (prod.snd : R ⨯ X ⟶ X) := by
  simp [familyComparison,Category.assoc]

omit [FinitaryExtensive C] [FinitaryExtensive D] [PreservesFiniteCoproducts F] in
@[reassoc] theorem familyComparison_inv_snd (X : C) :
    (familyComparison F b X).inv.left ≫ F.map (prod.snd : R ⨯ X ⟶ X)=prod.snd := by
  erw [← familyComparison_snd F b X,← Category.assoc]
  have h := congrArg Over.Hom.left (familyComparison F b X).inv_hom_id
  change (familyComparison F b X).inv.left ≫ (familyComparison F b X).hom.left=𝟙 _ at h
  erw [h,Category.id_comp]

/-- The actual slice functor compares constant families naturally in the
coefficient or recursive carrier, using the actual product comparison. -/
def familyNaturalIso :
    constantFamilyFunctor R ⋙ (functor F b) ≅
      F ⋙ constantFamilyFunctor Q := by
  refine NatIso.ofComponents (familyComparison F b) ?_
  intro X Y f
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · exact (Over.w _).trans (Over.w _).symm
  · change (F.map (prod.map (𝟙 R) f) ≫
        (familyComparison F b Y).hom.left) ≫ prod.snd =
      ((familyComparison F b X).hom.left ≫ prod.map (𝟙 Q) (F.map f)) ≫ prod.snd
    simp only [Category.assoc, prod.map_snd]
    erw [familyComparison_snd, ← F.map_comp,
      prod.map_snd, F.map_comp]
    erw [← Category.assoc, familyComparison_snd]

omit [FinitaryExtensive C] [FinitaryExtensive D] [PreservesFiniteCoproducts F] in
/-- The terminal comparison square needs only terminal uniqueness;
it does not invert a constant-family comparison. -/
theorem family_unit :
    terminalComparison (functor F b) ≫ constantUnitComparison Q =
      (functor F b).map (constantUnitComparison R) ≫
        (familyComparison F b (⊤_ C)).hom ≫
          (constantFamilyFunctor Q).map (terminalComparison F) := by
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · exact (Over.w _).trans (Over.w _).symm
  · exact terminalIsTerminal.hom_ext _ _

omit [FinitaryExtensive C] [FinitaryExtensive D] [PreservesFiniteCoproducts F] in
/-- The product square follows from naturality of the universal product
comparison. In particular, it compares the actual parameter projections. -/
theorem family_product (X Y : C) :
    prodComparison (functor F b)
        (constantFamily R X) (constantFamily R Y) ≫
      prod.map (familyComparison F b X).hom (familyComparison F b Y).hom ≫
        constantProductComparison Q (F.obj X) (F.obj Y) =
      (functor F b).map (constantProductComparison R X Y) ≫
        (familyComparison F b (X ⨯ Y)).hom ≫
          (constantFamilyFunctor Q).map (prodComparison F X Y) := by
  apply (cancel_mono
    (prodComparison (constantFamilyFunctor Q) (F.obj X) (F.obj Y))).mp
  simp only [Category.assoc,
    SyntaxParameterChange.constant_comparison_prodComparison, Category.comp_id]
  have hn := prodComparison_natural_of_natTrans (familyNaturalIso F b).hom
    (A := X) (B := Y)
  rw [prodComparison_comp, prodComparison_comp] at hn
  change (familyComparison F b (X ⨯ Y)).hom ≫
      ((constantFamilyFunctor Q).map (prodComparison F X Y) ≫
        prodComparison (constantFamilyFunctor Q) (F.obj X) (F.obj Y)) =
    ((functor F b).map
        (prodComparison (constantFamilyFunctor R) X Y) ≫
      prodComparison (functor F b)
        (constantFamily R X) (constantFamily R Y)) ≫
      prod.map (familyComparison F b X).hom (familyComparison F b Y).hom at hn
  rw [hn]
  simp only [Category.assoc]
  rw [← Category.assoc, ← Functor.map_comp,
    SyntaxParameterChange.constant_comparison_prodComparison,
    (functor F b).map_id, Category.id_comp]

/-- Coproduct coherence uses preserved coproducts of the finite-geometry functor.
No inverse of the constant-family coproduct comparison is used. -/
theorem family_sum (X Y : C) :
    inv (coprodComparison (functor F b)
      (constantFamily R X) (constantFamily R Y)) ≫
        coprod.map (familyComparison F b X).hom (familyComparison F b Y).hom ≫
          constantCoproductComparison Q (F.obj X) (F.obj Y) =
      (functor F b).map (constantCoproductComparison R X Y) ≫
        (familyComparison F b (X ⨿ Y)).hom ≫
          (constantFamilyFunctor Q).map (inv (coprodComparison F X Y)) := by
  apply (cancel_epi (coprodComparison (functor F b)
    (constantFamily R X) (constantFamily R Y))).mp
  rw [IsIso.hom_inv_id_assoc]
  apply coprod.hom_ext
  · simp only [coprod.inl_map_assoc, constantCoproductComparison,
      coprod.inl_desc, coprodComparison_inl_assoc]
    rw [← (functor F b).map_comp_assoc, coprod.inl_desc]
    erw [(familyNaturalIso F b).hom.naturality_assoc (coprod.inl : X ⟶ X ⨿ Y)]
    simp only [Functor.comp_map, ← Functor.map_comp, map_inl_inv_coprodComparison]
    rfl
  · simp only [coprod.inr_map_assoc, constantCoproductComparison,
      coprod.inr_desc, coprodComparison_inr_assoc]
    rw [← (functor F b).map_comp_assoc, coprod.inr_desc]
    erw [(familyNaturalIso F b).hom.naturality_assoc (coprod.inr : Y ⟶ X ⨿ Y)]
    simp only [Functor.comp_map, ← Functor.map_comp, map_inr_inv_coprodComparison]
    rfl

omit [FinitaryExtensive C] [FinitaryExtensive D] [PreservesFiniteCoproducts F] in
/-- Product coherence also allows arbitrary changes of the two
coefficient objects after applying the functor. -/
theorem family_product_map {X Y : C} {X' Y' : D}
    (u : F.obj X ⟶ X') (v : F.obj Y ⟶ Y') :
    prodComparison (functor F b)
        (constantFamily R X) (constantFamily R Y) ≫
      prod.map ((familyComparison F b X).hom ≫ (constantFamilyFunctor Q).map u)
        ((familyComparison F b Y).hom ≫ (constantFamilyFunctor Q).map v) ≫
          constantProductComparison Q X' Y' =
      (functor F b).map (constantProductComparison R X Y) ≫
        (familyComparison F b (X ⨯ Y)).hom ≫
          (constantFamilyFunctor Q).map (prodComparison F X Y ≫ prod.map u v) := by
  calc
    _ = (prodComparison (functor F b)
        (constantFamily R X) (constantFamily R Y) ≫
        prod.map (familyComparison F b X).hom (familyComparison F b Y).hom ≫
        constantProductComparison Q (F.obj X) (F.obj Y)) ≫
          (constantFamilyFunctor Q).map (prod.map u v) := by
      rw [← prod.map_map]
      simp only [Category.assoc, constantProductComparison_natural]
    _ = _ := by
      rw [family_product, Functor.map_comp]
      simp only [Category.assoc]

/-- The corresponding coproduct square uses only functoriality and the
universal coproduct injections, including when a coefficient is initial. -/
theorem family_sum_map {X Y : C} {X' Y' : D}
    (u : F.obj X ⟶ X') (v : F.obj Y ⟶ Y') :
    inv (coprodComparison (functor F b)
        (constantFamily R X) (constantFamily R Y)) ≫
      coprod.map ((familyComparison F b X).hom ≫ (constantFamilyFunctor Q).map u)
        ((familyComparison F b Y).hom ≫ (constantFamilyFunctor Q).map v) ≫
          constantCoproductComparison Q X' Y' =
      (functor F b).map (constantCoproductComparison R X Y) ≫
        (familyComparison F b (X ⨿ Y)).hom ≫
          (constantFamilyFunctor Q).map
            (inv (coprodComparison F X Y) ≫ coprod.map u v) := by
  calc
    _ = (inv (coprodComparison (functor F b)
        (constantFamily R X) (constantFamily R Y)) ≫
        coprod.map (familyComparison F b X).hom (familyComparison F b Y).hom ≫
        constantCoproductComparison Q (F.obj X) (F.obj Y)) ≫
          (constantFamilyFunctor Q).map (coprod.map u v) := by
      rw [← coprod.map_map]
      simp only [Category.assoc, constantCoproductComparison_natural]
    _ = _ := by
      rw [family_sum, Functor.map_comp]
      simp only [Category.assoc]

end CategoricalEssentialIncompleteness.V46.Miller.NamedSyntaxComparison.ParameterBaseChange
