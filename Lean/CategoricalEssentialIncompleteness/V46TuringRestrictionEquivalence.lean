/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46FullRestrictionProducts
public import CategoricalEssentialIncompleteness.V46CompatibleSplitSlices

/-! # Transfer of a split Turing structure along a restriction equivalence -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.RestrictionCategory RecursionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.TuringRestrictionEquivalence

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
variable [RestrictionCategory A] [RestrictionCategory B]

section Evaluator
variable (D : RestrictionProducts.ProductData B) {L Q : B} (j : L ≅ Q)
  (τ : D.prod Q Q ⟶ Q)
  (hτ : @IsTuringMorphism B inferInstance D.pcategoryStruct D.pcategoryLaws Q Q Q τ)

def conjugate : D.prod L L ⟶ L := D.map j.hom j.hom ≫ τ ≫ j.inv

include hτ in
theorem conjugate_turing : @IsTuringMorphism B inferInstance D.pcategoryStruct D.pcategoryLaws
    L L L (conjugate D j τ) := by
  intro X φ
  change D.prod X L ⟶ L at φ
  obtain ⟨g, hg, hcode⟩ := hτ X (D.map (𝟙 X) j.inv ≫ φ ≫ j.hom)
  change D.map g (𝟙 Q) ≫ τ = _ at hcode
  refine ⟨g ≫ j.inv, ?_, ?_⟩
  · change @PCategoryStruct.rst B inferInstance D.pcategoryStruct _ _ _ = 𝟙 X
    rw [D.restriction_eq]
    apply isTotal_comp _ (iso_total j.symm)
    change @PCategoryStruct.rst B inferInstance D.pcategoryStruct _ _ g = 𝟙 X at hg
    rwa [D.restriction_eq] at hg
  · change D.map (g ≫ j.inv) (𝟙 L) ≫ (D.map j.hom j.hom ≫ τ ≫ j.inv) = φ
    have he : D.map (g ≫ j.inv) (𝟙 L) ≫ D.map j.hom j.hom =
        D.map (𝟙 X) j.hom ≫ D.map g (𝟙 Q) := by
      rw [D.map_comp, D.map_comp]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
    rw [← Category.assoc, he, Category.assoc, ← Category.assoc (D.map g _), hcode]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [← Category.assoc, D.map_comp, Iso.hom_inv_id, Category.id_comp, D.map_id, Category.id_comp]
end Evaluator

variable (e : A ≌ B) (hF : PreservesRestriction e.functor)
variable (D : RestrictionProducts.ProductData B)
local notation "prodA" => fun X Y : A => e.inverse.obj (D.prod (e.functor.obj X) (e.functor.obj Y))
local notation "prodIso" => fun X Y : A =>
  e.counitIso.app (D.prod (e.functor.obj X) (e.functor.obj Y))

variable (Q : B) (τ : D.prod Q Q ⟶ Q)
variable (hτ : @IsTuringMorphism B inferInstance D.pcategoryStruct D.pcategoryLaws Q Q Q τ)
variable (univ : ∀ X : B, ∃ (j : X ⟶ Q) (s : Q ⟶ X),
  isTotal j ∧ j ≫ s = 𝟙 X ∧ s ≫ j = rst s)

include hF univ in
theorem universal (X : A) : ∃ (j : X ⟶ e.inverse.obj Q) (s : e.inverse.obj Q ⟶ X),
    isTotal j ∧ j ≫ s = 𝟙 X ∧ s ≫ j = rst s := by
  obtain ⟨a, b, ha, hab, hba⟩ := univ (e.functor.obj X)
  let k := e.counitIso.app Q
  let j : X ⟶ e.inverse.obj Q := e.functor.preimage (a ≫ k.inv)
  let s : e.inverse.obj Q ⟶ X := e.functor.preimage (k.hom ≫ b)
  have hj : e.functor.map j = a ≫ k.inv := e.functor.map_preimage _
  have hs : e.functor.map s = k.hom ≫ b := e.functor.map_preimage _
  refine ⟨j, s, hF.reflects_total _ (hj ▸ isTotal_comp ha (iso_total k.symm)), ?_, ?_⟩
  · apply e.functor.map_injective
    rw [e.functor.map_comp, hj, hs, e.functor.map_id]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, hab]
  · apply e.functor.map_injective
    rw [e.functor.map_comp, hj, hs, hF s, hs, Category.assoc, ← Category.assoc b, hba]
    have hr := rst_comp k.hom b
    rw [← Category.assoc, ← hr]
    simp

variable (Z : B) (terminate : ∀ X : B, X ⟶ Z)
  (ht : ∀ X, isTotal (terminate X))
  (hn : ∀ {X Y : B} (f : X ⟶ Y), f ≫ terminate Y = rst f ≫ terminate X)
  (hu : ∀ {X : B} (f : X ⟶ Z), isTotal f → f = terminate X)

def terminateMap (X : A) : X ⟶ e.inverse.obj Z :=
  e.functor.preimage (terminate (e.functor.obj X) ≫ (e.counitIso.app Z).inv)

include hF ht in
theorem terminate_total (X : A) : isTotal (terminateMap e Z terminate X) := by
  apply hF.reflects_total
  rw [terminateMap, e.functor.map_preimage]
  exact isTotal_comp (ht _) (iso_total (e.counitIso.app Z).symm)

include hF hn in
theorem terminate_naturality {X Y : A} (f : X ⟶ Y) :
    f ≫ terminateMap e Z terminate Y = rst f ≫ terminateMap e Z terminate X := by
  apply e.functor.map_injective
  rw [e.functor.map_comp, e.functor.map_comp, terminateMap, terminateMap,
    e.functor.map_preimage, e.functor.map_preimage,
    hF f, ← Category.assoc, hn, Category.assoc]

include hF hu in
theorem terminate_unique {X : A} (f : X ⟶ e.inverse.obj Z) (hf : isTotal f) :
    f = terminateMap e Z terminate X := by
  apply e.functor.map_injective
  rw [terminateMap, e.functor.map_preimage]
  have he := hu (e.functor.map f ≫ (e.counitIso.app Z).hom)
    (isTotal_comp (hF.total _ hf) (iso_total _))
  rw [← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable [Splits A]

def transport : CompatibleSplitSlices.TuringData A where
  products :=
    (FullRestrictionProducts.restrictionProducts e.functor hF D prodA prodIso).pcategoryStruct
  laws := (FullRestrictionProducts.restrictionProducts e.functor hF D prodA prodIso).pcategoryLaws
  restriction_eq :=
    RestrictionProducts.ProductData.restrictionCategory_eq _
  Q := e.inverse.obj Q
  evaluator := FullRestrictionProducts.evaluator e.functor D prodA prodIso (e.inverse.obj Q)
    (conjugate D (e.counitIso.app Q) τ)
  turing := FullRestrictionProducts.evaluator_isTuring e.functor hF D prodA prodIso _ _
    (conjugate_turing D (e.counitIso.app Q) τ hτ)
  universal := universal e hF Q univ
  terminal := e.inverse.obj Z
  terminate := terminateMap e Z terminate
  terminate_total := terminate_total e hF Z terminate ht
  terminate_self := (terminate_unique e hF Z terminate hu _ (rst_id _)).symm
  terminate_naturality := terminate_naturality e hF Z terminate hn
  terminate_unique := terminate_unique e hF Z terminate hu
  splittings := inferInstance

end CategoricalEssentialIncompleteness.V46.TuringRestrictionEquivalence
