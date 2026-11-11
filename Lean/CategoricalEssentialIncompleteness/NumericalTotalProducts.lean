/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.NumericalPartialProducts

/-!
# Total numerical pairing and categorical products

Partial pairing of total arrows is the mediating arrow of the numerical
product cone. The functor to PERs sends this pairing to the PER pairing,
through the proved product comparison isomorphism.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness
namespace Numerical

/-- Pairing of total numerical arrows is total. -/
theorem partialPair_isTotal {W X Y : Numerical} {f : W ⟶ X} {g : W ⟶ Y}
    (hf : RestrictionCategory.isTotal f) (hg : RestrictionCategory.isTotal g) :
    RestrictionCategory.isTotal (partialPair f g) := by
  change restrict (partialPair f g) = 𝟙 W
  rw [restrict_partialPair, show restrict f = 𝟙 W from hf,
    show restrict g = 𝟙 W from hg, Category.id_comp]

/-- Pairing in the original numerical total-arrow category. -/
def totalPair {W X Y : Total} (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ totalProduct X Y :=
  ⟨partialPair f.hom g.hom, partialPair_isTotal f.property g.property⟩

@[simp] theorem totalPair_fst {W X Y : Total} (f : W ⟶ X) (g : W ⟶ Y) :
    totalPair f g ≫ fst X Y = f := by
  apply WideSubcategory.hom_ext
  change partialPair f.hom g.hom ≫ partialFst X.obj Y.obj = f.hom
  rw [partialPair_fst, show restrict g.hom = 𝟙 W.obj from g.property, Category.id_comp]

@[simp] theorem totalPair_snd {W X Y : Total} (f : W ⟶ X) (g : W ⟶ Y) :
    totalPair f g ≫ snd X Y = g := by
  apply WideSubcategory.hom_ext
  change partialPair f.hom g.hom ≫ partialSnd X.obj Y.obj = g.hom
  rw [partialPair_snd, show restrict f.hom = 𝟙 W.obj from f.property, Category.id_comp]

/-- Total partial pairing agrees with the lift of the existing product cone. -/
theorem totalPair_eq_lift {W X Y : Total} (f : W ⟶ X) (g : W ⟶ Y) :
    totalPair f g = (productIsLimit X Y).lift (BinaryFan.mk f g) := by
  apply BinaryFan.IsLimit.hom_ext (productIsLimit X Y)
  · exact (totalPair_fst f g).trans
      ((productIsLimit X Y).fac (BinaryFan.mk f g) ⟨WalkingPair.left⟩).symm
  · exact (totalPair_snd f g).trans
      ((productIsLimit X Y).fac (BinaryFan.mk f g) ⟨WalkingPair.right⟩).symm

/-- The numerical functor preserves pairing through the product comparison. -/
theorem toPER_totalPair {W X Y : Total} (f : W ⟶ X) (g : W ⟶ Y) :
    toPER.map (totalPair f g) ≫ (productIso X Y).hom =
      NumericalPER.pair (toPER.map f) (toPER.map g) := by
  apply NumericalPER.product_hom_ext
  · rw [Category.assoc, productIso_hom_fst, ← toPER.map_comp,
      totalPair_fst, NumericalPER.pair_fst]
  · rw [Category.assoc, productIso_hom_snd, ← toPER.map_comp,
      totalPair_snd, NumericalPER.pair_snd]

end Numerical
end CategoricalEssentialIncompleteness
