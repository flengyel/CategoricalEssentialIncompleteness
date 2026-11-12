/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.LocalSwitch
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.CategoryTheory.Widesubcategory

/-! # Subobjects and restriction idempotents when monomorphisms have partial inverses -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.RestrictionSubobjects

variable (C : Type u) [Category.{v} C] [RestrictionCategory C]

abbrev Tot := WideSubcategory (isTotal (C := C))

/-- The partial-inverse hypothesis on total monomorphisms. -/
def MonoInverses : Prop :=
  ∀ {A B : Tot C} (m : A ⟶ B) [Mono m], ∃ r : B.obj ⟶ A.obj,
    m.hom ≫ r = 𝟙 A.obj ∧ r ≫ m.hom = rst r

variable {C} (h : MonoInverses C)

def inverse {A B : Tot C} (m : A ⟶ B) [Mono m] : B.obj ⟶ A.obj := (h m).choose

@[simp] theorem hom_inverse {A B : Tot C} (m : A ⟶ B) [Mono m] :
    m.hom ≫ inverse h m = 𝟙 A.obj := (h m).choose_spec.1

theorem inverse_hom {A B : Tot C} (m : A ⟶ B) [Mono m] :
    inverse h m ≫ m.hom = rst (inverse h m) := (h m).choose_spec.2

def domain {X : Tot C} (A : Subobject X) : Idem X.obj := Idem.ofRestrict (inverse h A.arrow)

theorem domain_hom {X : Tot C} (A : Subobject X) :
    (domain h A).hom = inverse h A.arrow ≫ A.arrow.hom := (inverse_hom h A.arrow).symm

theorem inclusion_domain {X : Tot C} (A : Subobject X) :
    A.arrow.hom ≫ (domain h A).hom = A.arrow.hom := by
  rw [domain_hom, ← Category.assoc, hom_inverse, Category.id_comp]

theorem domain_le_iff_fixed {X : Tot C} (A : Subobject X) (e : Idem X.obj) :
    domain h A ≤ e ↔ A.arrow.hom ≫ e.hom = A.arrow.hom := by
  constructor
  · intro he
    calc
      _ = (A.arrow.hom ≫ (domain h A).hom) ≫ e.hom := by rw [inclusion_domain]
      _ = A.arrow.hom ≫ (domain h A).hom := by rw [Category.assoc, Idem.le_def.mp he]
      _ = A.arrow.hom := inclusion_domain h A
  · intro he
    apply Idem.le_def.mpr
    rw [domain_hom, Category.assoc, he]

theorem domain_le_iff {X : Tot C} (A B : Subobject X) :
    domain h A ≤ domain h B ↔ A ≤ B := by
  rw [domain_le_iff_fixed]
  constructor
  · intro he
    let k := A.arrow.hom ≫ inverse h B.arrow
    have hk : k ≫ B.arrow.hom = A.arrow.hom := by
      simpa only [k, Category.assoc, ← domain_hom] using he
    have ht : isTotal k := by
      have hr := congrArg rst hk
      rw [rst_comp_of_isTotal _ B.arrow.property] at hr
      exact hr.trans A.arrow.property
    exact Subobject.le_of_comm (⟨k, ht⟩ : (A : Tot C) ⟶ (B : Tot C))
      (WideSubcategory.hom_ext _ hk)
  · intro he
    have hk : (Subobject.ofLE A B he).hom ≫ B.arrow.hom = A.arrow.hom :=
      congrArg (fun f => f.hom) (Subobject.ofLE_arrow he)
    rw [← hk, Category.assoc, inclusion_domain]

theorem domain_injective {X : Tot C} : Function.Injective (domain h (X := X)) := by
  intro A B he
  exact le_antisymm ((domain_le_iff h A B).mp he.le) ((domain_le_iff h B A).mp he.ge)

variable [Splits C]

theorem domain_surjective (X : Tot C) : Function.Surjective (domain h (X := X)) := by
  intro e
  obtain ⟨Z, m, r, ht, hmr, hrm⟩ := Splits.splitting e
  let Z' : Tot C := ⟨Z⟩
  let j : Z' ⟶ X := ⟨m, ht⟩
  have : Mono j := by
    constructor
    intro W f g hg
    apply WideSubcategory.hom_ext
    have hh := congrArg (fun k => k.hom ≫ r) hg
    change (f.hom ≫ m) ≫ r = (g.hom ≫ m) ≫ r at hh
    dsimp only [Z'] at f g hh ⊢
    simpa only [Category.assoc, hmr, Category.comp_id] using hh
  let A := Subobject.mk j
  let i := Subobject.underlyingIso j
  have hi : i.hom.hom ≫ m = A.arrow.hom := by
    exact congrArg (fun f => f.hom) (Subobject.underlyingIso_hom_comp_eq_mk j)
  have hi' : i.inv.hom ≫ A.arrow.hom = m := by
    have hp := congrArg (fun f => f.hom) i.inv_hom_id
    change i.inv.hom ≫ i.hom.hom = 𝟙 Z at hp
    rw [← hi, ← Category.assoc, hp, Category.id_comp]
  have hm : m ≫ e.hom = m := by rw [← hrm, ← Category.assoc, hmr, Category.id_comp]
  have hle : domain h A ≤ e := by
    apply (domain_le_iff_fixed h A e).mpr
    rw [← hi, Category.assoc, hm]
  have hfix : m ≫ (domain h A).hom = m := by
    rw [← hi', Category.assoc, inclusion_domain]
  have hge : e ≤ domain h A := by
    apply Idem.le_def.mpr
    rw [← hrm, Category.assoc, hfix]
  exact ⟨A, le_antisymm hle hge⟩

def orderIso (X : Tot C) : Subobject X ≃o Idem X.obj where
  toEquiv := Equiv.ofBijective (domain h) ⟨domain_injective h, domain_surjective h X⟩
  map_rel_iff' := domain_le_iff h _ _

@[simp] theorem orderIso_apply (X : Tot C) (A : Subobject X) :
    orderIso h X A = domain h A := rfl

end CategoricalEssentialIncompleteness.V46.RestrictionSubobjects
