/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ComputablePowers
public import CategoricalEssentialIncompleteness.V46RestrictionProductCones

/-! # Finite restriction products in the category of polynomial morphisms -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory PCategoryStruct PCategory RestrictionCategory
open CategoricalEssentialIncompleteness.V46.RestrictionProducts

namespace CategoricalEssentialIncompleteness.V46.ApplicativeSystem

universe v u
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
variable {A Z : C} (app : nearProd A A ⟶ A) (t : ∀ X : C, X ⟶ Z)

structure IsRestrictionTerminal : Prop where
  total (X : C) : isTotal (t X)
  domain {X : C} (f : X ⟶ Z) : f = PCategoryStruct.rst f ≫ t X

variable (unit : IsRestrictionTerminal t)

def formal (n : ℕ) : Powers app t := ⟨n⟩

def terminate (X : Powers app t) : X ⟶ formal app t 0 := ⟨t _, .terminate X.arity⟩

include unit in
theorem terminate_total (X : Powers app t) : isTotal (terminate app t X) := by
  apply Subtype.ext
  exact unit.total _

include unit in
theorem terminate_domain {X : Powers app t} (f : X ⟶ formal app t 0) :
    f = RestrictionCategory.rst f ≫ terminate app t X :=
  Subtype.ext (unit.domain f.val)

def unitCone (X : Powers app t) : Cone X (formal app t 0) :=
  Cone.unitRight (terminate app t) (terminate_total app t unit) (terminate_domain app t unit) X

theorem product_hom_ext {W X Y : C} {f g : W ⟶ nearProd X Y}
    (h₁ : f ≫ p0 _ _ = g ≫ p0 _ _) (h₂ : f ≫ p1 _ _ = g ≫ p1 _ _) : f = g :=
  (eq_partialPairing_of_proj h₁ h₂).trans (partialPairing_proj g)

def successorCone (k : ℕ) : Cone (formal app t (k+1)) (formal app t 1) where
  obj := formal app t (k+2)
  fst := ⟨p0 _ _, .first k⟩
  snd := ⟨p1 _ _, .last k⟩
  fst_total := Subtype.ext (p0_isTotal _ _)
  snd_total := Subtype.ext (p1_isTotal _ _)
  lift f g _ := ⟨partialPairing f.val g.val, f.property.pair g.property⟩
  lift_fst f g h := by
    have eqn : PCategoryStruct.rst f.val = PCategoryStruct.rst g.val := congrArg Subtype.val h
    apply Subtype.ext
    change partialPairing f.val g.val ≫ p0 _ _ = f.val
    rw [p0_partialPairing, ← eqn]
    exact rst_comp_self _
  lift_snd f g h := by
    have eqn : PCategoryStruct.rst f.val = PCategoryStruct.rst g.val := congrArg Subtype.val h
    apply Subtype.ext
    change partialPairing f.val g.val ≫ p1 _ _ = g.val
    rw [p1_partialPairing, eqn]
    exact rst_comp_self _
  hom_ext f g h₁ h₂ := Subtype.ext (product_hom_ext
    (congrArg Subtype.val h₁) (congrArg Subtype.val h₂))

def lastCone : (n : ℕ) → Cone (formal app t n) (formal app t 1)
  | 0 => (unitCone app t unit (formal app t 1)).swap
  | n+1 => successorCone app t n

def finitePowerCone (X : Powers app t) : (m : ℕ) → Cone X (formal app t m)
  | 0 => unitCone app t unit X
  | 1 => lastCone app t unit X.arity
  | n+2 => Cone.associate (finitePowerCone X (n+1)) (successorCone app t n)
      (lastCone app t unit (finitePowerCone X (n+1)).obj.arity)

def products : ProductData (Powers app t) :=
  Cone.productData fun X Y => finitePowerCone app t unit X Y.arity

/-- At a nonempty input power the pairing with the last variable is the ambient
partial pairing. Its domain is the intersection of the two component domains. -/
theorem successor_pair (k : ℕ) {W : Powers app t} (f : W ⟶ formal app t (k+1))
    (g : W ⟶ formal app t 1) :
    ((successorCone app t k).pair f g).val = partialPairing f.val g.val := by
  apply product_hom_ext
  · exact (congrArg Subtype.val ((successorCone app t k).pair_fst f g)).trans
      (p0_partialPairing f.val g.val).symm
  · exact (congrArg Subtype.val ((successorCone app t k).pair_snd f g)).trans
      (p1_partialPairing f.val g.val).symm

end CategoricalEssentialIncompleteness.V46.ApplicativeSystem
