/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ComputablePowerRetractions

/-! # A partial combinatory algebra is a Turing object for its computable morphisms

In Cockett and Hofstra, Theorem 4.9(i), a total prefix of a code supplies the
parameter morphism. Binary coding and decoding make every formal finite power
a retract of the formal first power.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory PCategoryStruct PCategory RecursionCategory RestrictionCategory
open CategoricalEssentialIncompleteness.V46.RestrictionProducts

namespace CategoricalEssentialIncompleteness.V46.ApplicativeSystem

universe v u
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
variable {A Z : C} (app : nearProd A A ⟶ A) (t : ∀ X : C, X ⟶ Z)
variable (unit : IsRestrictionTerminal t)

def application : (products app t unit).prod (formal app t 1) (formal app t 1) ⟶ formal app t 1 :=
  ⟨app, .application⟩

theorem map_last {X : Powers app t} (g : X ⟶ formal app t 1) :
    ((products app t unit).map g (𝟙 (formal app t 1))).val =
      partialPairing ((lastCone app t unit X.arity).fst.val ≫ g.val)
        (lastCone app t unit X.arity).snd.val := by
  change ((successorCone app t 0).pair ((lastCone app t unit _).fst ≫ g)
    ((lastCone app t unit _).snd ≫ 𝟙 _)).val = _
  rw [Category.comp_id, successor_pair]
  rfl

theorem exists_parameter (complete : CombinatoriallyComplete app t) (X : Powers app t)
    (f : (products app t unit).prod X (formal app t 1) ⟶ formal app t 1) :
    ∃ g : X ⟶ formal app t 1, isTotal g ∧
      (products app t unit).map g (𝟙 (formal app t 1)) ≫ application app t unit = f := by
  obtain ⟨n⟩ := X
  cases n with
  | zero =>
    obtain ⟨p, hp, eqn⟩ := complete 1 f.val f.property
    let g : formal app t 0 ⟶ formal app t 1 := ⟨p, .point p hp⟩
    refine ⟨g, Subtype.ext hp, Subtype.ext ?_⟩
    change ((products app t unit).map g (𝟙 _)).val ≫ app = f.val
    rw [map_last]
    exact eqn
  | succ n =>
    obtain ⟨p, hp, ht, eqn⟩ := complete (n+2) f.val f.property
    let g : formal app t (n+1) ⟶ formal app t 1 :=
      ⟨applyPositive app t p n, applyPositive_polynomial app t p hp n⟩
    refine ⟨g, Subtype.ext ht, Subtype.ext ?_⟩
    change ((products app t unit).map g (𝟙 _)).val ≫ app = f.val
    rw [map_last]
    change nearProd_map (applyPositive app t p n) (𝟙 A) ≫ app = f.val at eqn
    rw [nearProd_eq_partialPairing, Category.comp_id] at eqn
    exact eqn

/-- The displayed application is Turing among the actual morphisms of the
computable category, for every formal parameter power including the empty power. -/
theorem application_isTuring (complete : CombinatoriallyComplete app t) :
    let D := products app t unit
    @IsTuringMorphism (Powers app t) _ D.pcategoryStruct D.pcategoryLaws _ _ _
      (application app t unit) := by
  dsimp only
  intro X f
  obtain ⟨g, hg, eqn⟩ := exists_parameter app t unit complete X f
  refine ⟨g, ?_, eqn⟩
  change @PCategoryStruct.rst (Powers app t) _ (products app t unit).pcategoryStruct _ _ g = 𝟙 _
  rw [(products app t unit).restriction_eq]
  exact hg

/-- The formal first power with the given application is a Turing object. Every
ordered pair of formal input and output powers has a corresponding Turing morphism. -/
theorem structure_of_pca (complete : CombinatoriallyComplete app t) :
    let D := products app t unit
    letI : PCategoryStruct (Powers app t) := D.pcategoryStruct
    letI : PCategory (Powers app t) := D.pcategoryLaws
    IsTuringMorphism (W := formal app t 1) (X := formal app t 1) (Y := formal app t 1)
      (application app t unit) ∧
      ∀ X Y : Powers app t, ∃ τ : nearProd (formal app t 1) X ⟶ Y, IsTuringMorphism τ := by
  let D := products app t unit
  let : PCategoryStruct (Powers app t) := D.pcategoryStruct
  let : PCategory (Powers app t) := D.pcategoryLaws
  have h := application_isTuring app t unit complete
  refine ⟨h, (turingObject_iff (formal app t 1)).mpr ⟨⟨_, h⟩, ?_⟩⟩
  intro X
  obtain ⟨m, r, hm, hr⟩ := powers_retract app t unit complete X
  refine ⟨m, r, ?_, hr⟩
  change @PCategoryStruct.rst (Powers app t) _ D.pcategoryStruct _ _ m = 𝟙 _
  rw [D.restriction_eq]
  exact hm

end CategoricalEssentialIncompleteness.V46.ApplicativeSystem
