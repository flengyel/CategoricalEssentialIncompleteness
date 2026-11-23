/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.StandardTrueTheory
public import CategoricalEssentialIncompleteness.V46PartialMapTotals
public import CategoricalEssentialIncompleteness.V46PrintedObjectCoding
public import Mathlib.CategoryTheory.IsoCat

/-! # Isomorphisms for total partial maps and standard interpretation -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits FFL.FirstOrder.Arithmetic
open FailureOfComposition FailureOfComposition.TypedProgramCategory FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46

namespace PartialMaps
variable {D : Type*} [Category* D] [HasPullbacks D]

/-- Take the ordinary value of a total partial span. -/
def fromTotal : Tot D ⥤ D where
  obj X := X.obj.obj
  map f := totalValue f.hom f.property
  map_id X := by
    apply @ofTotal_injective D _ _ X.obj X.obj
    rw [ofTotal_totalValue, ofTotal_id]
    rfl
  map_comp {X _ Z} f g := by
    apply @ofTotal_injective D _ _ X.obj Z.obj
    rw [ofTotal_totalValue, ofTotal_comp, ofTotal_totalValue, ofTotal_totalValue]
    rfl

/-- Total partial maps and their underlying morphisms give inverse functors. -/
def totalIsomorphism : IsoCat D (Tot D) where
  functor := toTotal
  inverse := fromTotal
  unit_eq := by
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro X Y f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact (totalValue_ofTotal (X := Par.mk X) (Y := Par.mk Y) f).symm
  counit_eq := by
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro X Y f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    apply WideSubcategory.hom_ext
    exact ofTotal_totalValue f.hom f.property

end PartialMaps

namespace PrintedObjectCoding
variable (T : FFL.FirstOrder.ArithmeticTheory) [𝗣𝗔 ⪯ T]

/-- Restore the guarded triple using its original source and target object terms. -/
def guarded : NormalizedCategory T ⥤ CodedProgramCategory T where
  obj X := object T X
  map {X Y} f := (isoToOmega T X).hom ≫ f.hom ≫ (isoToOmega T Y).inv
  map_id X := by change (isoToOmega T X).hom ≫ 𝟙 _ ≫ (isoToOmega T X).inv = _; simp
  map_comp {X Y Z} f g := by
    change (isoToOmega T X).hom ≫ (f.hom ≫ g.hom) ≫ (isoToOmega T Z).inv =
      ((isoToOmega T X).hom ≫ f.hom ≫ (isoToOmega T Y).inv) ≫
      (isoToOmega T Y).hom ≫ g.hom ≫ (isoToOmega T Z).inv
    simp only [Category.assoc, Iso.inv_hom_id_assoc]

def normalization : IsoCat (CodedProgramCategory T) (NormalizedCategory T) where
  functor := comparison T
  inverse := guarded T
  unit_eq := by
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro X Y f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    change f = (isoToOmega T (objectCode X)).hom ≫
      ((isoToOmega T (objectCode X)).inv ≫ f ≫ (isoToOmega T (objectCode Y)).hom) ≫
      (isoToOmega T (objectCode Y)).inv
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  counit_eq := by
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro X Y f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    apply InducedCategory.hom_ext
    change (isoToOmega T X).inv ≫ ((isoToOmega T X).hom ≫ f.hom ≫ (isoToOmega T Y).inv) ≫
      (isoToOmega T Y).hom = f.hom
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

end PrintedObjectCoding

namespace TrueArithmetic

instance : StandardTrueTheory.comparison.IsIso where
  bijective_obj := Function.bijective_iff_has_inverse.mpr
    ⟨fun Y => object 𝗧𝗔 (objectCode Y.base), fun _ => rfl, fun _ => rfl⟩

/-- Standard interpretation on the object terms with the manuscript's numerical coding. -/
def interpretation : PrintedObjectCoding.NormalizedCategory 𝗧𝗔 ⥤ ClassicalPrograms.Rec :=
  PrintedObjectCoding.guarded 𝗧𝗔 ⋙ StandardTrueTheory.comparison

def interpretationIsomorphism :
    IsoCat (PrintedObjectCoding.NormalizedCategory 𝗧𝗔) ClassicalPrograms.Rec :=
  (PrintedObjectCoding.normalization 𝗧𝗔).symm.trans StandardTrueTheory.comparison.asIsomorphism

theorem interpretation_object (X : STObjectCode) :
    interpretation.obj X = ⟨object 𝗣𝗔 X⟩ := rfl

theorem interpretation_value {X Y : PrintedObjectCoding.NormalizedCategory 𝗧𝗔} (f : X ⟶ Y) :
    (interpretation.map f).val =
      (SyntacticModel.modelFunctor 𝗧𝗔 ℕ).map ((PrintedObjectCoding.guarded 𝗧𝗔).map f) := rfl

end TrueArithmetic
end CategoricalEssentialIncompleteness.V46
