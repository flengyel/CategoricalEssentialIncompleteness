/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46RestrictionProductCategory
public import CategoricalEssentialIncompleteness.RestrictionFunctorEquivalences
public import PCats.Recursion

/-! # Binary restriction products in a full restriction subcategory -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.FullRestrictionProducts

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
variable [RestrictionCategory A] [RestrictionCategory B]
variable (F : A ⥤ B) [F.Full] [F.Faithful] (hF : PreservesRestriction F)
variable (D : RestrictionProducts.ProductData B) (prod : A → A → A)
variable (i : ∀ X Y, F.obj (prod X Y) ≅ D.prod (F.obj X) (F.obj Y))

def first (X Y : A) : prod X Y ⟶ X := F.preimage ((i X Y).hom ≫ D.fst _ _)
def second (X Y : A) : prod X Y ⟶ Y := F.preimage ((i X Y).hom ≫ D.snd _ _)
def pair {V X Y : A} (f : V ⟶ X) (g : V ⟶ Y) : V ⟶ prod X Y :=
  F.preimage (D.pair (F.map f) (F.map g) ≫ (i X Y).inv)

omit [RestrictionCategory A] [F.Faithful] in
theorem first_value (X Y : A) :
    F.map (first F D prod i X Y) = (i X Y).hom ≫ D.fst _ _ := F.map_preimage _
omit [RestrictionCategory A] [F.Faithful] in
theorem second_value (X Y : A) :
    F.map (second F D prod i X Y) = (i X Y).hom ≫ D.snd _ _ := F.map_preimage _
omit [RestrictionCategory A] [F.Faithful] in
theorem pair_value {V X Y : A} (f : V ⟶ X) (g : V ⟶ Y) :
    F.map (pair F D prod i f g) = D.pair (F.map f) (F.map g) ≫ (i X Y).inv :=
  F.map_preimage _

include hF in
theorem first_total (X Y : A) : isTotal (first F D prod i X Y) := by
  apply hF.reflects_total
  rw [first_value]
  exact isTotal_comp (iso_total _) (D.fst_total _ _)

include hF in
theorem second_total (X Y : A) : isTotal (second F D prod i X Y) := by
  apply hF.reflects_total
  rw [second_value]
  exact isTotal_comp (iso_total _) (D.snd_total _ _)

include hF in
theorem pair_fst {V X Y : A} (f : V ⟶ X) (g : V ⟶ Y) :
    pair F D prod i f g ≫ first F D prod i X Y = rst g ≫ f := by
  apply F.map_injective
  rw [F.map_comp, pair_value, first_value, Category.assoc,
    ← Category.assoc (i X Y).inv, Iso.inv_hom_id, Category.id_comp,
    D.pair_fst, F.map_comp, hF g]

include hF in
theorem pair_snd {V X Y : A} (f : V ⟶ X) (g : V ⟶ Y) :
    pair F D prod i f g ≫ second F D prod i X Y = rst f ≫ g := by
  apply F.map_injective
  rw [F.map_comp, pair_value, second_value, Category.assoc,
    ← Category.assoc (i X Y).inv, Iso.inv_hom_id, Category.id_comp,
    D.pair_snd, F.map_comp, hF f]

include hF in
theorem pair_restriction {V X Y : A} (f : V ⟶ X) (g : V ⟶ Y) :
    rst (pair F D prod i f g) = rst f ≫ rst g := by
  apply F.map_injective
  have hi : isTotal (i X Y).inv := iso_total (i X Y).symm
  rw [hF _, pair_value, rst_comp_of_isTotal _ hi,
    D.pair_restriction, F.map_comp, hF f, hF g]

omit [RestrictionCategory A] in
theorem pair_proj {V X Y : A} (h : V ⟶ prod X Y) :
    pair F D prod i (h ≫ first F D prod i X Y) (h ≫ second F D prod i X Y) = h := by
  apply F.map_injective
  rw [pair_value, F.map_comp, first_value, F.map_comp, second_value]
  simp only [← Category.assoc]
  rw [D.pair_proj, Category.assoc, Iso.hom_inv_id, Category.comp_id]

def restrictionProducts : RestrictionProducts.ProductData A where
  prod := prod
  fst := first F D prod i
  snd := second F D prod i
  pair := pair F D prod i
  fst_total := first_total F hF D prod i
  snd_total := second_total F hF D prod i
  pair_fst := pair_fst F hF D prod i
  pair_snd := pair_snd F hF D prod i
  pair_restriction := pair_restriction F hF D prod i
  pair_proj := pair_proj F D prod i

theorem map_comparison {W X Y Z : A} (f : W ⟶ X) (g : Y ⟶ Z) :
    F.map ((restrictionProducts F hF D prod i).map f g) ≫ (i X Z).hom =
      (i W Y).hom ≫ D.map (F.map f) (F.map g) := by
  change F.map (pair F D prod i (first F D prod i W Y ≫ f)
    (second F D prod i W Y ≫ g)) ≫ (i X Z).hom = _
  rw [pair_value, F.map_comp, first_value, F.map_comp, second_value,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simpa only [RestrictionProducts.ProductData.map, Category.assoc] using (D.comp_pair (i W Y).hom
    (D.fst _ _ ≫ F.map f) (D.snd _ _ ≫ F.map g)).symm

def evaluator (Q : A) (τ : D.prod (F.obj Q) (F.obj Q) ⟶ F.obj Q) : prod Q Q ⟶ Q :=
  F.preimage ((i Q Q).hom ≫ τ)

theorem evaluator_isTuring (Q : A) (τ : D.prod (F.obj Q) (F.obj Q) ⟶ F.obj Q)
    (hτ : @RecursionCategory.IsTuringMorphism B inferInstance D.pcategoryStruct D.pcategoryLaws
      (F.obj Q) (F.obj Q) (F.obj Q) τ) :
    @RecursionCategory.IsTuringMorphism A inferInstance
      (restrictionProducts F hF D prod i).pcategoryStruct
      (restrictionProducts F hF D prod i).pcategoryLaws Q Q Q (evaluator F D prod i Q τ) := by
  intro X φ
  change prod X Q ⟶ Q at φ
  obtain ⟨g, hg, hcode⟩ := hτ (F.obj X) ((i X Q).inv ≫ F.map φ)
  change D.map g (𝟙 (F.obj Q)) ≫ τ = (i X Q).inv ≫ F.map φ at hcode
  have hg' : isTotal g := by
    change @PCategoryStruct.rst B inferInstance D.pcategoryStruct _ _ g = 𝟙 _ at hg
    rwa [D.restriction_eq] at hg
  let a : X ⟶ Q := F.preimage g
  have ha : F.map a = g := F.map_preimage _
  refine ⟨a, ?_, ?_⟩
  · change @PCategoryStruct.rst A inferInstance
      (restrictionProducts F hF D prod i).pcategoryStruct X Q a = 𝟙 X
    rw [(restrictionProducts F hF D prod i).restriction_eq]
    apply hF.reflects_total
    rw [ha]
    exact hg'
  · change (restrictionProducts F hF D prod i).map a (𝟙 Q) ≫ evaluator F D prod i Q τ = φ
    apply F.map_injective
    rw [F.map_comp]
    change F.map ((restrictionProducts F hF D prod i).map a (𝟙 Q)) ≫
      F.map (F.preimage ((i Q Q).hom ≫ τ)) = F.map φ
    rw [F.map_preimage, ← Category.assoc, map_comparison, ha, F.map_id,
      Category.assoc, hcode, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end CategoricalEssentialIncompleteness.V46.FullRestrictionProducts

namespace CategoricalEssentialIncompleteness.V46.RestrictionProducts.ProductData

variable {C : Type u₁} [Category.{v₁} C] [RestrictionCategory C] (D : ProductData C)

def mapIso {X X' Y Y' : C} (i : X ≅ X') (j : Y ≅ Y') : D.prod X Y ≅ D.prod X' Y' where
  hom := D.map i.hom j.hom
  inv := D.map i.inv j.inv
  hom_inv_id := by rw [D.map_comp, i.hom_inv_id, j.hom_inv_id, D.map_id]
  inv_hom_id := by rw [D.map_comp, i.inv_hom_id, j.inv_hom_id, D.map_id]

end CategoricalEssentialIncompleteness.V46.RestrictionProducts.ProductData
