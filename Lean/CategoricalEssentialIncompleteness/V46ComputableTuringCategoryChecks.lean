/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ComputableTuringCategory
public import CategoricalEssentialIncompleteness.V46ComputablePowerRestriction
public import CategoricalEssentialIncompleteness.V46ComputablePowerInclusion

/-! # Cockett and Hofstra's structure theorem for Turing categories

Definition 4.2 tests the equality of partial morphisms, including the domain.
Theorem 4.9 applies to the cartesian restriction category of computable morphisms
on formal powers. In its converse the class of idempotents contains all identities.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Idempotents PCategoryStruct RecursionCategory RestrictionCategory
open CategoricalEssentialIncompleteness.V46.ApplicativeSystem

namespace CategoricalEssentialIncompleteness.V46.ComputableTuringCategoryChecks

universe v u
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
variable {A Z : C} (app : nearProd A A ⟶ A) (t : ∀ X : C, X ⟶ Z)

theorem code_with_prefix (n : ℕ) (p : Z ⟶ A) (f : power Z A (n+2) ⟶ A) :
    Codes app t p (n+2) f ↔ isTotal p ∧ isTotal (applyPositive app t p n) ∧
      applyPositive app t p (n+1) = f := Iff.rfl

theorem positive_input_domain (n : ℕ) (f : power Z A (n+1) ⟶ Z) :
    Computable app t (n+1) 0 f ↔ Computable app t (n+1) (n+1) (PCategoryStruct.rst f) := Iff.rfl

/-- At the empty input and output power, the scalar is the restriction of an
evaluated total point. The terminal equation identifies each scalar with its domain. -/
theorem scalar_domain (unit : IsRestrictionTerminal t) (f : Z ⟶ Z) :
    Computable app t 0 0 f ↔
      ∃ p : Z ⟶ A, isTotal p ∧ f = PCategoryStruct.rst (p ≫ diag A ≫ app) := by
  have tid : t Z = 𝟙 Z := by
    simpa only [PCategory.rst_id, Category.id_comp] using (unit.domain (𝟙 Z)).symm
  have scalar : f = PCategoryStruct.rst f := by
    simpa only [tid, Category.comp_id] using unit.domain f
  constructor
  · rintro ⟨g, dom, p, hp, rfl⟩
    exact ⟨p, hp, scalar.trans dom⟩
  · rintro ⟨p, hp, h⟩
    exact ⟨p ≫ diag A ≫ app, scalar.symm.trans h, p, hp, rfl⟩

theorem combinatory_completeness (unit : IsRestrictionTerminal t) :
    CombinatoriallyComplete app t ↔
      ∀ (n m : ℕ) (f : power Z A n ⟶ power Z A m), Polynomial app t n m f →
        Computable app t n m f := by
  constructor
  · intro h n m f hf
    exact (polynomial_iff_computable app t h unit.domain n m f).mp hf
  · intro h n f hf
    exact h n 1 f hf

/-- The terminal morphism is inherited. Every ambient object can be the source
of a pair of morphisms in the binary product universal property. -/
theorem finite_products (unit : IsRestrictionTerminal t) (X Y : Powers app t) :
    let F := inclusion app t
    let D := products app t unit
    F.map (terminate app t X) = t (F.obj X) ∧
      ∀ {W : C} (f : W ⟶ F.obj X) (g : W ⟶ F.obj Y), PCategoryStruct.rst f = PCategoryStruct.rst g →
        ∃! h : W ⟶ F.obj (D.prod X Y), h ≫ F.map (D.fst X Y) = f ∧ h ≫ F.map (D.snd X Y) = g :=
  ⟨rfl, fun f g h => inclusion_product app t unit X Y f g h⟩

/-- The parameters for the original application are total computable morphisms
at every arity. The same first power is a Turing object at all input and output types. -/
theorem pca_turing (unit : IsRestrictionTerminal t)
    (complete : ∀ (n m : ℕ) (f : power Z A n ⟶ power Z A m),
      Polynomial app t n m f → Computable app t n m f) :
    let D := products app t unit
    letI : PCategoryStruct (Powers app t) := D.pcategoryStruct
    letI : PCategory (Powers app t) := D.pcategoryLaws
    (∀ (X : Powers app t) (f : nearProd X (formal app t 1) ⟶ formal app t 1),
      ∃ g : X ⟶ formal app t 1, isTotal g ∧
        nearProd_map g (𝟙 (formal app t 1)) ≫ application app t unit = f) ∧
      ∀ X Y : Powers app t, ∃ a : nearProd (formal app t 1) X ⟶ Y, IsTuringMorphism a := by
  have h := (combinatory_completeness app t unit).mpr complete
  exact ⟨exists_parameter app t unit h, (structure_of_pca app t unit h).2⟩

/-- For a designated Turing application, every finite-power morphism is computable.
The equivalence splits precisely the idempotents already split in the ambient
category. Its two functors preserve restriction. -/
theorem turing_representation (unit : IsRestrictionTerminal t)
    (typed : ∀ X Y : C, ∃ a : nearProd A X ⟶ Y, IsTuringMorphism a)
    (designated : IsTuringMorphism app) :
    CombinatoriallyComplete app t ∧
    (∀ (n m : ℕ) (f : power Z A n ⟶ power Z A m), Computable app t n m f) ∧
    (∀ X : Powers app t, IdempotentSplitting.splitsIn (inclusion app t) ((toKaroubi _).obj X)) ∧
    ∃ e : C ≌ (IdempotentSplitting.splitsIn (inclusion app t)).FullSubcategory,
      (∀ {X Y : C} (f : X ⟶ Y), e.functor.map (PCategoryStruct.rst f) = rst (e.functor.map f)) ∧
      (∀ {P Q} (f : P ⟶ Q), e.inverse.map (rst f) = PCategoryStruct.rst (e.inverse.map f)) := by
  have retracts (X : C) : ∃ (i : X ⟶ A) (r : A ⟶ X), i ≫ r = 𝟙 X := by
    obtain ⟨i, r, _, eqn⟩ := ((turingObject_iff A).mp typed).2 X
    exact ⟨i, r, eqn⟩
  obtain ⟨complete, compute, _⟩ := structure_of_turing app t designated (unit.total A) unit.domain retracts
  exact ⟨complete, compute, IdempotentSplitting.identity_mem (inclusion app t),
    representation app t designated (unit.total A) unit.domain retracts,
    representation_restrictions app t designated (unit.total A) unit.domain retracts⟩

#print axioms code_with_prefix
#print axioms positive_input_domain
#print axioms scalar_domain
#print axioms combinatory_completeness
#print axioms finite_products
#print axioms pca_turing
#print axioms turing_representation

end CategoricalEssentialIncompleteness.V46.ComputableTuringCategoryChecks
