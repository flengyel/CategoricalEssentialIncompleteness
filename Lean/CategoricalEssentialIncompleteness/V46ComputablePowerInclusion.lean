/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ComputablePowerProducts

/-! # The inclusion of the computable powers preserves finite restriction products

The image of each product cone satisfies the restriction-product universal
property for morphisms from every object of the ambient category.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory RestrictionCategory
open CategoricalEssentialIncompleteness.V46.RestrictionProducts

namespace CategoricalEssentialIncompleteness.V46.ApplicativeSystem

universe v u
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
variable {A Z : C} (app : PCategoryStruct.nearProd A A ⟶ A) (t : ∀ X : C, X ⟶ Z)

def IsRestrictionProduct {B X Y : C} (p : B ⟶ X) (q : B ⟶ Y) : Prop :=
  ∀ {W : C} (f : W ⟶ X) (g : W ⟶ Y), rst f = rst g →
    ∃! h : W ⟶ B, h ≫ p = f ∧ h ≫ q = g

private theorem Cone.isProduct {X Y : C} (P : Cone X Y) : IsRestrictionProduct P.fst P.snd := by
  intro W f g eqn
  exact ⟨P.lift f g eqn, ⟨P.lift_fst f g eqn, P.lift_snd f g eqn⟩,
    fun h prop => P.hom_ext h _ (prop.1.trans (P.lift_fst f g eqn).symm)
      (prop.2.trans (P.lift_snd f g eqn).symm)⟩

private noncomputable def underlyingCone {X Y : Powers app t} (P : Cone X Y)
    (univ : IsRestrictionProduct P.fst.val P.snd.val) :
    Cone ((inclusion app t).obj X) ((inclusion app t).obj Y) where
  obj := (inclusion app t).obj P.obj
  fst := P.fst.val
  snd := P.snd.val
  fst_total := congrArg Subtype.val P.fst_total
  snd_total := congrArg Subtype.val P.snd_total
  lift f g h := (univ f g h).choose
  lift_fst f g h := (univ f g h).choose_spec.1.1
  lift_snd f g h := (univ f g h).choose_spec.1.2
  hom_ext f g eq₀ eq₁ := by
    have dom : rst (g ≫ P.fst.val) = rst (g ≫ P.snd.val) := by
      rw [rst_comp_of_isTotal g (congrArg Subtype.val P.fst_total),
        rst_comp_of_isTotal g (congrArg Subtype.val P.snd_total)]
    exact (univ _ _ dom).unique ⟨eq₀, eq₁⟩ ⟨rfl, rfl⟩

private theorem unit_product (unit : IsRestrictionTerminal t) (X : Powers app t) :
    IsRestrictionProduct (unitCone app t unit X).fst.val (unitCone app t unit X).snd.val :=
  Cone.isProduct (Cone.unitRight t unit.total unit.domain ((inclusion app t).obj X))

private theorem swap_product {X Y : Powers app t} (P : Cone X Y)
    (h : IsRestrictionProduct P.fst.val P.snd.val) : IsRestrictionProduct P.snd.val P.fst.val :=
  Cone.isProduct (underlyingCone app t P h).swap

private theorem near_product (X Y : C) :
    IsRestrictionProduct (PCategoryStruct.p0 X Y) (PCategoryStruct.p1 X Y) := by
  intro W f g eqn
  change PCategoryStruct.rst f = PCategoryStruct.rst g at eqn
  have fst : PCategoryStruct.partialPairing f g ≫ PCategoryStruct.p0 _ _ = f := by
    rw [PCategory.p0_partialPairing, ← eqn]
    exact rst_comp_self f
  have snd : PCategoryStruct.partialPairing f g ≫ PCategoryStruct.p1 _ _ = g := by
    rw [PCategory.p1_partialPairing, eqn]
    exact rst_comp_self g
  exact ⟨_, ⟨fst, snd⟩, fun h eqs =>
    product_hom_ext (eqs.1.trans fst.symm) (eqs.2.trans snd.symm)⟩

private theorem successor_product (n : ℕ) : IsRestrictionProduct
    (successorCone app t n).fst.val (successorCone app t n).snd.val :=
  near_product (positivePower A n) A

private theorem last_product (unit : IsRestrictionTerminal t) :
    ∀ n, IsRestrictionProduct (lastCone app t unit n).fst.val (lastCone app t unit n).snd.val
  | 0 => swap_product app t _ (unit_product app t unit (formal app t 1))
  | n+1 => successor_product app t n

private theorem associate_product {X Y V : Powers app t} (P : Cone X Y) (Q : Cone Y V)
    (R : Cone P.obj V) (hp : IsRestrictionProduct P.fst.val P.snd.val)
    (hq : IsRestrictionProduct Q.fst.val Q.snd.val) (hr : IsRestrictionProduct R.fst.val R.snd.val) :
    IsRestrictionProduct (Cone.associate P Q R).fst.val (Cone.associate P Q R).snd.val := by
  let p := underlyingCone app t P hp
  let q := underlyingCone app t Q hq
  let r := underlyingCone app t R hr
  let a := Cone.associate p q r
  have dom : rst (r.fst ≫ p.snd) = rst r.snd :=
    (isTotal_comp r.fst_total p.snd_total).trans r.snd_total.symm
  have snd : a.snd = (Cone.associate P Q R).snd.val := by
    apply q.hom_ext
    · exact (q.lift_fst _ _ dom).trans (congrArg Subtype.val (Q.lift_fst (R.fst ≫ P.snd) R.snd _)).symm
    · exact (q.lift_snd _ _ dom).trans (congrArg Subtype.val (Q.lift_snd (R.fst ≫ P.snd) R.snd _)).symm
  change IsRestrictionProduct a.fst (Cone.associate P Q R).snd.val
  rw [← snd]
  exact Cone.isProduct a

private theorem finite_power_product (unit : IsRestrictionTerminal t) (X : Powers app t) :
    ∀ m, IsRestrictionProduct (finitePowerCone app t unit X m).fst.val
      (finitePowerCone app t unit X m).snd.val
  | 0 => unit_product app t unit X
  | 1 => last_product app t unit X.arity
  | n+2 => associate_product app t _ _ _ (finite_power_product unit X (n+1))
      (successor_product app t n) (last_product app t unit _)

theorem inclusion_product (unit : IsRestrictionTerminal t) (X Y : Powers app t) :
    IsRestrictionProduct ((inclusion app t).map ((products app t unit).fst X Y))
      ((inclusion app t).map ((products app t unit).snd X Y)) :=
  finite_power_product app t unit X Y.arity

end CategoricalEssentialIncompleteness.V46.ApplicativeSystem
