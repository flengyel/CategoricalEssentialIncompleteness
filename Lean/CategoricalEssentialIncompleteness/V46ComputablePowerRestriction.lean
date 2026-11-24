/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46TuringComputablePowers
public import CategoricalEssentialIncompleteness.V46KaroubiRestriction

/-! # Restriction under the equivalence obtained by splitting computable idempotents -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Idempotents RestrictionCategory

namespace CategoricalEssentialIncompleteness.V46.IdempotentSplitting

universe v w u z
variable {B : Type u} {C : Type z} [Category.{v} B] [Category.{w} C]
variable [RestrictionCategory B] [RestrictionCategory C]

instance (P : ObjectProperty B) : RestrictionCategory P.FullSubcategory where
  rst f := ObjectProperty.homMk (rst f.hom)
  rst_comp_self f := ObjectProperty.hom_ext _ (rst_comp_self f.hom)
  rst_comm f g := ObjectProperty.hom_ext _ (rst_comm f.hom g.hom)
  rst_comp_rst f g := ObjectProperty.hom_ext _ (rst_comp_rst f.hom g.hom)
  rst_comp f g := ObjectProperty.hom_ext _ (rst_comp f.hom g.hom)

variable (F : B ⥤ C)

omit [RestrictionCategory B] in
theorem Splitting.inclusion_total {P : Karoubi B} (s : Splitting F P) : isTotal s.i := by
  change rst s.i = 𝟙 _
  have e := congrArg (fun k => k ≫ s.r) (rst_comp_self s.i)
  simpa only [Category.assoc, s.section_retraction, Category.comp_id] using e

/-- Realizing a morphism between split objects preserves the Karoubi restriction
`P.p ≫ rst f.f`. The section of each actual splitting is total. -/
theorem realization_restriction (preserves : ∀ {X Y : B} (f : X ⟶ Y), F.map (rst f) = rst (F.map f))
    {P Q : (splitsIn F).FullSubcategory} (f : P ⟶ Q) :
    (realization F).map (rst f) = rst ((realization F).map f) := by
  let a := splitting F P
  let b := splitting F Q
  let k := F.map f.hom.f
  have target : k ≫ F.map Q.obj.p = k := by rw [← F.map_comp, Karoubi.comp_p]
  have inclusion : ((a.i ≫ k) ≫ b.r) ≫ b.i = a.i ≫ k := by
    simp only [Category.assoc, b.factor, target]
  have dom : rst ((a.i ≫ k) ≫ b.r) = rst (a.i ≫ k) :=
    (rst_comp_of_isTotal _ (b.inclusion_total F)).symm.trans (congrArg rst inclusion)
  have domain_formula := congrArg (fun u => u ≫ a.r) (rst_comp a.i k)
  change a.i ≫ F.map (P.obj.p ≫ rst f.hom.f) ≫ a.r = rst (a.i ≫ k ≫ b.r)
  rw [← Category.assoc a.i k, dom, F.map_comp, preserves, ← a.factor]
  change a.i ≫ ((a.r ≫ a.i) ≫ rst k) ≫ a.r = rst (a.i ≫ k)
  simp only [Category.assoc, a.section_retraction_assoc] at ⊢
  simp only [Category.assoc, a.section_retraction, Category.comp_id] at domain_formula
  exact domain_formula.symm

end CategoricalEssentialIncompleteness.V46.IdempotentSplitting

namespace CategoricalEssentialIncompleteness.V46.ApplicativeSystem

universe v u
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
variable {A Z : C} (app : PCategoryStruct.nearProd A A ⟶ A) (t : ∀ X : C, X ⟶ Z)

theorem realization_preserves_restriction
    {P Q : (IdempotentSplitting.splitsIn (inclusion app t)).FullSubcategory} (f : P ⟶ Q) :
    (IdempotentSplitting.realization (inclusion app t)).map (rst f) =
      rst ((IdempotentSplitting.realization (inclusion app t)).map f) :=
  IdempotentSplitting.realization_restriction _ (fun _ => rfl) f

/-- Both functors in the representation of a Turing category preserve restriction. -/
theorem representation_restrictions (universal : RecursionCategory.IsTuringMorphism app)
    (ht : isTotal (t A)) (unit : ∀ {X : C} (f : X ⟶ Z), f = PCategoryStruct.rst f ≫ t X)
    (retracts : ∀ X : C, ∃ (i : X ⟶ A) (r : A ⟶ X), i ≫ r = 𝟙 X) :
    let e := representation app t universal ht unit retracts
    (∀ {X Y : C} (f : X ⟶ Y), e.functor.map (rst f) = rst (e.functor.map f)) ∧
    (∀ {P Q} (f : P ⟶ Q), e.inverse.map (rst f) = rst (e.inverse.map f)) := by
  let e := representation app t universal ht unit retracts
  have preserves {P Q} (f : P ⟶ Q) : e.inverse.map (rst f) = rst (e.inverse.map f) :=
    realization_preserves_restriction app t f
  exact ⟨fun f => LocalConnectedness.V46.equivalence_inverse_preserves e.symm
    (fun g => preserves g) f, fun f => preserves f⟩

end CategoricalEssentialIncompleteness.V46.ApplicativeSystem
