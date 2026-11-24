/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46RestrictionProductCategory

/-! # Restriction products formed from the empty power and successive binary powers -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.V46.RestrictionProducts

universe v u
variable {D : Type u} [Category.{v} D] [RestrictionCategory D]

/-- A restriction product characterized by pairs of morphisms with equal domain. -/
structure Cone (X Y : D) where
  obj : D
  fst : obj ⟶ X
  snd : obj ⟶ Y
  fst_total : isTotal fst
  snd_total : isTotal snd
  lift {W : D} (f : W ⟶ X) (g : W ⟶ Y) (h : rst f = rst g) : W ⟶ obj
  lift_fst {W : D} (f : W ⟶ X) (g : W ⟶ Y) (h : rst f = rst g) : lift f g h ≫ fst = f
  lift_snd {W : D} (f : W ⟶ X) (g : W ⟶ Y) (h : rst f = rst g) : lift f g h ≫ snd = g
  hom_ext {W : D} (f g : W ⟶ obj) : f ≫ fst = g ≫ fst → f ≫ snd = g ≫ snd → f = g

namespace Cone

variable {X Y Z : D}

theorem domain_lift (P : Cone X Y) {W : D} (f : W ⟶ X) (g : W ⟶ Y) (h : rst f = rst g) :
    rst (P.lift f g h) = rst f := by
  rw [← rst_comp_of_isTotal (P.lift f g h) P.fst_total, P.lift_fst]

def pair (P : Cone X Y) {W : D} (f : W ⟶ X) (g : W ⟶ Y) : W ⟶ P.obj :=
  P.lift (rst g ≫ f) (rst f ≫ g) (by rw [rst_comp_rst, rst_comp_rst, rst_comm])

theorem pair_fst (P : Cone X Y) {W : D} (f : W ⟶ X) (g : W ⟶ Y) :
    P.pair f g ≫ P.fst = rst g ≫ f := P.lift_fst _ _ _

theorem pair_snd (P : Cone X Y) {W : D} (f : W ⟶ X) (g : W ⟶ Y) :
    P.pair f g ≫ P.snd = rst f ≫ g := P.lift_snd _ _ _

theorem dom_pair (P : Cone X Y) {W : D} (f : W ⟶ X) (g : W ⟶ Y) :
    rst (P.pair f g) = rst f ≫ rst g := by
  rw [pair, domain_lift, rst_comp_rst, rst_comm]

theorem pair_projections (P : Cone X Y) {W : D} (h : W ⟶ P.obj) :
    P.pair (h ≫ P.fst) (h ≫ P.snd) = h := by
  apply P.hom_ext
  · rw [pair_fst, rst_comp_of_isTotal h P.snd_total, ← Category.assoc, rst_comp_self]
  · rw [pair_snd, rst_comp_of_isTotal h P.fst_total, ← Category.assoc, rst_comp_self]

def swap (P : Cone X Y) : Cone Y X where
  obj := P.obj
  fst := P.snd
  snd := P.fst
  fst_total := P.snd_total
  snd_total := P.fst_total
  lift f g h := P.lift g f h.symm
  lift_fst f g h := P.lift_snd g f h.symm
  lift_snd f g h := P.lift_fst g f h.symm
  hom_ext f g h₁ h₂ := P.hom_ext f g h₂ h₁

def unitRight (t : ∀ X : D, X ⟶ Z) (total : ∀ X, isTotal (t X))
    (unit : ∀ {W : D} (f : W ⟶ Z), f = rst f ≫ t W) (X : D) : Cone X Z where
  obj := X
  fst := 𝟙 X
  snd := t X
  fst_total := rst_id X
  snd_total := total X
  lift f _ _ := f
  lift_fst f _ _ := Category.comp_id f
  lift_snd f g h := by
    calc
      f ≫ t X = rst (f ≫ t X) ≫ t _ := unit _
      _ = g := by rw [rst_comp_of_isTotal f (total X), h, ← unit g]
  hom_ext f g h _ := by simpa only [Category.comp_id] using h

def assocSnd (P : Cone X Y) (Q : Cone Y Z) (R : Cone P.obj Z) : R.obj ⟶ Q.obj :=
  Q.lift (R.fst ≫ P.snd) R.snd
    ((isTotal_comp R.fst_total P.snd_total).trans R.snd_total.symm)

def assocLift (P : Cone X Y) (Q : Cone Y Z) (R : Cone P.obj Z) {W : D}
    (f : W ⟶ X) (g : W ⟶ Q.obj) (h : rst f = rst g) : W ⟶ R.obj :=
  let feq : rst f = rst (g ≫ Q.fst) := h.trans (rst_comp_of_isTotal g Q.fst_total).symm
  let a := P.lift f (g ≫ Q.fst) feq
  R.lift a (g ≫ Q.snd)
    ((P.domain_lift _ _ feq).trans (h.trans (rst_comp_of_isTotal g Q.snd_total).symm))

/-- Products of X and Y, of Y and Z, and of (X × Y) and Z
give a product of X and (Y × Z). -/
def associate (P : Cone X Y) (Q : Cone Y Z) (R : Cone P.obj Z) : Cone X Q.obj where
  obj := R.obj
  fst := R.fst ≫ P.fst
  snd := assocSnd P Q R
  fst_total := isTotal_comp R.fst_total P.fst_total
  snd_total := (Q.domain_lift _ _ _).trans (isTotal_comp R.fst_total P.snd_total)
  lift f g h := assocLift P Q R f g h
  lift_fst f g h := by
    simp only [assocLift, ← Category.assoc, R.lift_fst, P.lift_fst]
  lift_snd f g h := by
    apply Q.hom_ext
    · simp only [Category.assoc, assocSnd, Q.lift_fst]
      simp only [← Category.assoc, assocLift, R.lift_fst, P.lift_snd]
    · simp only [Category.assoc, assocSnd, Q.lift_snd, assocLift, R.lift_snd]
  hom_ext f g h₁ h₂ := by
    apply R.hom_ext
    · apply P.hom_ext
      · simpa only [Category.assoc] using h₁
      · have e := congrArg (fun k => k ≫ Q.fst) h₂
        simpa only [Category.assoc, assocSnd, Q.lift_fst] using e
    · have e := congrArg (fun k => k ≫ Q.snd) h₂
      simpa only [Category.assoc, assocSnd, Q.lift_snd] using e

def productData (cone : ∀ X Y : D, Cone X Y) : ProductData D where
  prod X Y := (cone X Y).obj
  fst X Y := (cone X Y).fst
  snd X Y := (cone X Y).snd
  pair f g := (cone _ _).pair f g
  fst_total X Y := (cone X Y).fst_total
  snd_total X Y := (cone X Y).snd_total
  pair_fst f g := (cone _ _).pair_fst f g
  pair_snd f g := (cone _ _).pair_snd f g
  pair_restriction f g := (cone _ _).dom_pair f g
  pair_proj h := (cone _ _).pair_projections h

end Cone
end CategoricalEssentialIncompleteness.V46.RestrictionProducts
