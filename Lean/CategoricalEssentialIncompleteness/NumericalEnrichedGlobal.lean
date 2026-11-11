/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.NumericalEnriched
public import CategoricalEssentialIncompleteness.GlobalTotals

/-!
# Global arrows of the numerical Set-enrichment

Evaluation at the unique element of the terminal type identifies global arrows
with numerical partial recursive arrows. Constant families give the inverse
functor. The comparison preserves restriction, zeros, and partial products,
and restricts to an equivalence of the total-arrow categories.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness
namespace Numerical

/-- Evaluate a global numerical arrow at the unique point of the terminal type. -/
def globalEvaluation : enrichedRestriction.GlobalCategory ⥤ Numerical where
  obj X := X.obj
  map f := (TypeCat.Hom.hom f) default
  map_id X := enriched_identity_apply X.obj default
  map_comp f g := enriched_comp_apply f g default

/-- Regard a numerical arrow as a constant global family. -/
def globalConstants : Numerical ⥤ enrichedRestriction.GlobalCategory where
  obj X := enrichedRestriction.globalObject X
  map f := ↾fun _ ↦ f
  map_id X := by
    apply ConcreteCategory.hom_ext (C := Type)
    intro t
    exact (enriched_identity_apply X t).symm
  map_comp f g := by
    apply ConcreteCategory.hom_ext (C := Type)
    intro t
    exact (enriched_comp_apply (↾fun _ ↦ f) (↾fun _ ↦ g) t).symm

@[simp] theorem globalEvaluation_map {X Y : enrichedRestriction.GlobalCategory}
    (f : X ⟶ Y) : globalEvaluation.map f = (TypeCat.Hom.hom f) default := rfl

@[simp] theorem globalConstants_map {X Y : Numerical} (f : X ⟶ Y)
    (t : ⊤_ (Type)) : (TypeCat.Hom.hom (globalConstants.map f)) t = f := rfl

@[simp] theorem globalConstants_globalEvaluation
    {X Y : enrichedRestriction.GlobalCategory} (f : X ⟶ Y) :
    globalConstants.map (globalEvaluation.map f) = f := by
  apply ConcreteCategory.hom_ext (C := Type)
  intro t
  exact ConcreteCategory.congr_arg (C := Type) f (Subsingleton.elim _ _)

@[simp] theorem globalEvaluation_globalConstants {X Y : Numerical} (f : X ⟶ Y) :
    globalEvaluation.map (globalConstants.map f) = f := rfl

/-- The global partial-arrow category of the Set-enrichment is equivalent to
the numerical category. -/
def enrichedGlobalEquivalence : enrichedRestriction.GlobalCategory ≌ Numerical where
  functor := globalEvaluation
  inverse := globalConstants
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro X Y f
    simpa only [Functor.id_map, Functor.comp_map, Iso.refl_hom,
      Category.id_comp, Category.comp_id] using (globalConstants_globalEvaluation f).symm)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro X Y f
    simpa only [Functor.id_map, Functor.comp_map, Iso.refl_hom,
      Category.id_comp, Category.comp_id] using globalEvaluation_globalConstants f)
  functor_unitIso_comp X := by
    change (𝟙 X.obj : X.obj ⟶ X.obj) ≫ 𝟙 X.obj = 𝟙 X.obj
    exact Category.id_comp _

/-- Evaluation preserves the restriction of a global arrow. -/
@[simp] theorem globalEvaluation_restrict {X Y : enrichedRestriction.GlobalCategory}
    (f : X ⟶ Y) :
    globalEvaluation.map (RestrictionCategory.rst f) = restrict (globalEvaluation.map f) := rfl

/-- Evaluation preserves zero morphisms. -/
@[simp] theorem globalEvaluation_zero (X Y : enrichedRestriction.GlobalCategory) :
    globalEvaluation.map (0 : X ⟶ Y) = 0 := rfl

/-- The global partial pairing evaluates to numerical partial pairing. -/
@[simp] theorem globalEvaluation_pair {X Y Z : Numerical}
    (f : enrichedRestriction.globalObject X ⟶ enrichedRestriction.globalObject Y)
    (g : enrichedRestriction.globalObject X ⟶ enrichedRestriction.globalObject Z) :
    globalEvaluation.map (enrichedHom.pair f g) =
      partialPair (globalEvaluation.map f) (globalEvaluation.map g) :=
  enriched_pair_apply f g default

@[simp] theorem globalEvaluation_fst (X Y : Numerical) :
    globalEvaluation.map (enrichedHom.fst X Y) = partialFst X Y := rfl

@[simp] theorem globalEvaluation_snd (X Y : Numerical) :
    globalEvaluation.map (enrichedHom.snd X Y) = partialSnd X Y := rfl

/-- Evaluate global total arrows as total numerical arrows. -/
def globalTotalEvaluation : enrichedRestriction.GlobalTotal ⥤ Total where
  obj X := totalObject X.obj.obj
  map {X Y} f :=
    { hom := (TypeCat.Hom.hom f.hom) default
      property := by
        change restrict ((TypeCat.Hom.hom f.hom) default) = 𝟙 _
        have hf : enrichedRestriction.restrict f.hom = enrichedHom.identity X.obj.obj := f.property
        have h := ConcreteCategory.congr_hom (C := Type) hf default
        simpa only [enriched_restrict_apply, enriched_identity_apply] using h }
  map_id X := by
    apply WideSubcategory.hom_ext
    exact enriched_identity_apply X.obj.obj default
  map_comp f g := by
    apply WideSubcategory.hom_ext
    exact enriched_comp_apply f.hom g.hom default

/-- Constant families of total numerical arrows are global total arrows. -/
def globalTotalConstants : Total ⥤ enrichedRestriction.GlobalTotal where
  obj X := enrichedRestriction.totalGlobalObject X.obj
  map f :=
    { hom := ↾fun _ ↦ f.hom
      property := by
        apply ConcreteCategory.hom_ext (C := Type)
        intro t
        exact f.property }
  map_id X := by
    apply WideSubcategory.hom_ext
    apply ConcreteCategory.hom_ext (C := Type)
    intro t
    exact (enriched_identity_apply X.obj t).symm
  map_comp f g := by
    apply WideSubcategory.hom_ext
    apply ConcreteCategory.hom_ext (C := Type)
    intro t
    exact (enriched_comp_apply (↾fun _ ↦ f.hom) (↾fun _ ↦ g.hom) t).symm

@[simp] theorem globalTotalEvaluation_map {X Y : enrichedRestriction.GlobalTotal}
    (f : X ⟶ Y) : (globalTotalEvaluation.map f).hom =
      (TypeCat.Hom.hom f.hom) default := rfl

@[simp] theorem globalTotalConstants_map {X Y : Total} (f : X ⟶ Y)
    (t : ⊤_ (Type)) : (TypeCat.Hom.hom (globalTotalConstants.map f).hom) t = f.hom := rfl

@[simp] theorem globalTotalConstants_globalTotalEvaluation
    {X Y : enrichedRestriction.GlobalTotal} (f : X ⟶ Y) :
    globalTotalConstants.map (globalTotalEvaluation.map f) = f := by
  apply WideSubcategory.hom_ext
  apply ConcreteCategory.hom_ext (C := Type)
  intro t
  exact ConcreteCategory.congr_arg (C := Type) f.hom (Subsingleton.elim _ _)

@[simp] theorem globalTotalEvaluation_globalTotalConstants {X Y : Total} (f : X ⟶ Y) :
    globalTotalEvaluation.map (globalTotalConstants.map f) = f := by
  apply WideSubcategory.hom_ext
  rfl

/-- The equivalence on global arrows restricts to the total-arrow categories. -/
def enrichedGlobalTotalEquivalence : enrichedRestriction.GlobalTotal ≌ Total where
  functor := globalTotalEvaluation
  inverse := globalTotalConstants
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro X Y f
    simpa only [Functor.id_map, Functor.comp_map, Iso.refl_hom,
      Category.id_comp, Category.comp_id] using
        (globalTotalConstants_globalTotalEvaluation f).symm)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro X Y f
    simpa only [Functor.id_map, Functor.comp_map, Iso.refl_hom,
      Category.id_comp, Category.comp_id] using globalTotalEvaluation_globalTotalConstants f)
  functor_unitIso_comp X := by
    change globalTotalEvaluation.map (𝟙 X) ≫ 𝟙 _ = _
    simp

/-- Evaluation of global total arrows preserves binary products. -/
instance globalTotalEvaluationPreservesBinaryProducts :
    PreservesLimitsOfShape (Discrete WalkingPair) globalTotalEvaluation :=
  inferInstanceAs
    (PreservesLimitsOfShape (Discrete WalkingPair) enrichedGlobalTotalEquivalence.functor)

end Numerical
end CategoricalEssentialIncompleteness
