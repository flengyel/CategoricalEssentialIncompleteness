/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.NumericalPCategory
public import CategoricalEssentialIncompleteness.NumericalTotalProducts
public import PCats.DomTotalEmbedding
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Comparison of the numerical total-arrow categories

The restriction induced by the numerical P-category and the original numerical
restriction have the same total morphisms. The comparison functors preserve the
underlying morphisms and identify the two product pairings.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness
namespace Numerical

/-- Total morphisms for the induced restriction, regarded as original numerical total
morphisms. -/
def fromPCategoryTotal : RestrictionCategory.TotalSubcategory Numerical ⥤ Total where
  obj X := totalObject X.obj
  map f := ⟨f.hom, (pcategory_rst_eq f.hom).symm.trans f.property⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Original numerical total morphisms, regarded as total morphisms for the induced
restriction. -/
def toPCategoryTotal : Total ⥤ RestrictionCategory.TotalSubcategory Numerical where
  obj X := ⟨X.obj⟩
  map f := ⟨f.hom, (pcategory_rst_eq f.hom).trans f.property⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The two total-arrow categories are equivalent by functors with unchanged underlying
morphisms. -/
def pcategoryTotalEquivalence : RestrictionCategory.TotalSubcategory Numerical ≌ Total where
  functor := fromPCategoryTotal
  inverse := toPCategoryTotal
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro X Y f
    apply WideSubcategory.hom_ext
    change f.hom ≫ 𝟙 Y.obj = 𝟙 X.obj ≫ f.hom
    simp)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro X Y f
    apply WideSubcategory.hom_ext
    change f.hom ≫ 𝟙 Y.obj = 𝟙 X.obj ≫ f.hom
    simp)
  functor_unitIso_comp X := by
    change fromPCategoryTotal.map (𝟙 X) ≫ 𝟙 _ = _
    simp

/-- The comparison identifies P-category pairing with the original numerical total pairing. -/
theorem fromPCategoryTotal_pairing
    {W X Y : RestrictionCategory.TotalSubcategory Numerical} (f : W ⟶ X) (g : W ⟶ Y) :
    fromPCategoryTotal.map (RestrictionCategory.TotalSubcategory.binaryProductLift f g) =
      totalPair (fromPCategoryTotal.map f) (fromPCategoryTotal.map g) := by
  apply WideSubcategory.hom_ext
  exact pcategory_partialPairing_eq f.hom g.hom

/-- The comparison equivalence preserves binary products. -/
theorem fromPCategoryTotal_preservesBinaryProducts :
    PreservesLimitsOfShape (Discrete WalkingPair) fromPCategoryTotal := by
  change PreservesLimitsOfShape (Discrete WalkingPair) pcategoryTotalEquivalence.functor
  infer_instance

end Numerical
end CategoricalEssentialIncompleteness
