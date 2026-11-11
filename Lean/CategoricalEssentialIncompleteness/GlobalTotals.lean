/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.GlobalCartesian
public import CategoricalEssentialIncompleteness.EnrichedDomains
public import Mathlib.CategoryTheory.Widesubcategory
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Global total arrows

The ordinary restriction category is the category of global arrows of the
enriched restriction structure. Its total arrows form the wide subcategory
defined by the existing `RestrictionCategory.isTotal` property. The finite-limit
comparison extends to an equivalence of categories, preserving binary products.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe v u w
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness
namespace EnrichedRestriction
variable {V : Type u} [Category.{v} V] [HasFiniteLimits V] {O : Type w}
variable {H : InternalHom V O} (R : EnrichedRestriction H)

/-- The manuscript's underlying ordinary restriction category `K₀`. -/
abbrev GlobalCategory := R.Parameterized (⊤_ V)

/-- Its wide subcategory of total arrows. -/
abbrev GlobalTotal := WideSubcategory (RestrictionCategory.isTotal (C := R.GlobalCategory))

def globalObject (X : O) : R.GlobalCategory := ⟨X⟩
def totalGlobalObject (X : O) : R.GlobalTotal := ⟨R.globalObject X⟩

/-- A point of the totality pullback gives a total arrow of `K₀`. -/
def globalTotalArrow {X Y : O} (f : ⊤_ V ⟶ R.totalObject X Y) :
    R.totalGlobalObject X ⟶ R.totalGlobalObject Y :=
  ⟨(f ≫ R.totalι X Y : ⊤_ V ⟶ H.hom X Y), R.total_condition f⟩

/-- A total arrow of `K₀` lifts to a global point of the totality pullback. -/
def globalTotalPoint {X Y : R.GlobalTotal} (f : X ⟶ Y) :
    ⊤_ V ⟶ R.totalObject X.obj.obj Y.obj.obj := R.totalLift f.hom f.property

@[simp] theorem globalTotalPoint_ι {X Y : R.GlobalTotal} (f : X ⟶ Y) :
    R.globalTotalPoint f ≫ R.totalι X.obj.obj Y.obj.obj = f.hom := by
  simp [globalTotalPoint]

variable (products : R.Products)

/-- The inclusion of the totality pullbacks induces a functor on global arrows. -/
def toGlobalTotal : (R.totalHom products).Global ⥤ R.GlobalTotal where
  obj X := R.totalGlobalObject X.obj
  map := R.globalTotalArrow
  map_id X := by
    apply WideSubcategory.hom_ext
    exact R.total_identity_ι products X.obj
  map_comp f g := by
    apply WideSubcategory.hom_ext
    exact R.total_comp_ι products f g

/-- The inverse functor is given by the pullback universal property. -/
def fromGlobalTotal : R.GlobalTotal ⥤ (R.totalHom products).Global where
  obj X := ⟨X.obj.obj⟩
  map := R.globalTotalPoint
  map_id X := by
    apply (cancel_mono (R.totalι X.obj.obj X.obj.obj)).mp
    change R.globalTotalPoint (𝟙 X) ≫ R.totalι _ _ =
      (R.totalHom products).identity X.obj.obj ≫ R.totalι _ _
    simp only [R.globalTotalPoint_ι, R.total_identity_ι]
    rfl
  map_comp {X Y Z} f g := by
    apply (cancel_mono (R.totalι X.obj.obj Z.obj.obj)).mp
    change R.globalTotalPoint (f ≫ g) ≫ R.totalι _ _ =
      (R.totalHom products).comp (R.globalTotalPoint f) (R.globalTotalPoint g) ≫ R.totalι _ _
    simp only [R.globalTotalPoint_ι, R.total_comp_ι]
    rfl

@[simp] theorem from_toGlobalTotal_map
    {X Y : (R.totalHom products).Global} (f : X ⟶ Y) :
    (R.fromGlobalTotal products).map ((R.toGlobalTotal products).map f) = f := by
  apply (cancel_mono (R.totalι X.obj Y.obj)).mp
  exact R.globalTotalPoint_ι (R.globalTotalArrow f)

@[simp] theorem to_fromGlobalTotal_map {X Y : R.GlobalTotal} (f : X ⟶ Y) :
    (R.toGlobalTotal products).map ((R.fromGlobalTotal products).map f) = f := by
  apply WideSubcategory.hom_ext
  exact R.globalTotalPoint_ι f

/-- Global points of the internal total hom-objects form `Tot(K₀)`. -/
def globalTotalEquivalence : (R.totalHom products).Global ≌ R.GlobalTotal where
  functor := R.toGlobalTotal products
  inverse := R.fromGlobalTotal products
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro X Y f
    simpa only [Functor.id_map, Functor.comp_map, Iso.refl_hom,
      Category.id_comp, Category.comp_id] using (R.from_toGlobalTotal_map products f).symm)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro X Y f
    simpa only [Functor.id_map, Functor.comp_map, Iso.refl_hom,
      Category.id_comp, Category.comp_id] using R.to_fromGlobalTotal_map products f)
  functor_unitIso_comp X := by
    change (R.toGlobalTotal products).map (𝟙 X) ≫ 𝟙 _ = _
    simp

/-- Binary products exist in the ordinary total-arrow category by the comparison. -/
theorem globalTotalHasBinaryProducts (products : R.Products) : HasBinaryProducts R.GlobalTotal :=
  Adjunction.hasLimitsOfShape_of_equivalence (R.globalTotalEquivalence products).inverse

/-- The global comparison preserves binary products. -/
theorem globalTotalPreservesBinaryProducts :
    PreservesLimitsOfShape (Discrete WalkingPair) (R.globalTotalEquivalence products).functor :=
  inferInstance

variable [R.Zeros]

/-- The internal zero arrows induce zero morphisms in every parameterized category. -/
instance parameterizedZeroMorphisms (T : V) : HasZeroMorphisms (R.Parameterized T) where
  zero X Y := ⟨R.zeroAt T X.obj Y.obj⟩
  comp_zero := fun {_X _Y} f _Z ↦ Zeros.comp_zero f
  zero_comp := fun _X {_Y _Z} f ↦ Zeros.zero_comp f

/-- Nontriviality in `K₀` is exactly inequality of the enriched identity and zero. -/
theorem global_nontrivial_iff (X : O) :
    (𝟙 (R.globalObject X) : R.globalObject X ⟶ R.globalObject X) ≠ 0 ↔
      H.unit X ≠ Zeros.zero R X X := by
  change H.identity X ≠ R.zeroAt (⊤_ V) X X ↔ _
  simp only [InternalHom.identity, zeroAt,
    terminalIsTerminal.hom_ext (terminal.from (⊤_ V)) (𝟙 (⊤_ V)), Category.id_comp]

end EnrichedRestriction
end CategoricalEssentialIncompleteness
