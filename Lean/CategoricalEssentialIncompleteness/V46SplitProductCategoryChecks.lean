/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SplitProductCategory

/-! # The full product laws and compatibility with restriction -/

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.RestrictionCategory PCategoryStruct
open CategoricalEssentialIncompleteness.LocalConnectedness SplitObject

variable {R : Type u} [Category.{v} R] [PCategoryStruct R] [PCategory R]

attribute [local instance] productData productLaws

example : PCategory (SplitObject R) := productLaws

example {X Y : SplitObject R} (f : X ⟶ Y) :
    @PCategoryStruct.rst (SplitObject R) inferInstance productData X Y f =
      CategoryTheory.RestrictionCategory.rst f := productData_restriction f

example {X Y Z : SplitObject R} (f : X ⟶ Y) (g : Y ⟶ Z) :
    nearProd_map f (𝟙 X) ≫ nearProd_map g (𝟙 X) = nearProd_map (f ≫ g) (𝟙 X) := by
  rw [PCategory.nearProd_comp, Category.id_comp]

example [CategoryTheory.Limits.HasZeroMorphisms R] [RecursionCategory.Prodominical R] :
    RecursionCategory.Prodominical (SplitObject R) := prodominicalLaws

#print axioms SplitObject.productLaws
#print axioms SplitObject.prodominicalLaws
#print axioms SplitObject.productData_assoc_hom
#print axioms SplitObject.productData_swap_hom
