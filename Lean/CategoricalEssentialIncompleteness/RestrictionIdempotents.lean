/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import PCats.Restriction
public import Mathlib.Order.Lattice

/-!
# Restriction idempotents and inverse image

Composition is diagrammatic: `f ≫ g` applies `f` first. The order on
restriction idempotents is `a ≤ b` if `a ≫ b = a`.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness

variable {C : Type u} [Category.{v} C] [RestrictionCategory C]

theorem restrict_restrict {X Y : C} (f : X ⟶ Y) : rst (rst f) = rst f := by
  simpa only [Category.comp_id, rst_id] using rst_comp_rst f (𝟙 X)

theorem total_of_comp_total {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : isTotal (f ≫ g)) : isTotal f := by
  have ha := rst_comp_absorb f g
  rw [show rst (f ≫ g) = 𝟙 X from h, Category.comp_id] at ha
  exact ha

theorem iso_total {X Y : C} (i : X ≅ Y) : isTotal i.hom :=
  total_of_comp_total i.hom i.inv (by rw [i.hom_inv_id]; exact rst_id X)

/-- A restriction idempotent on `X`. -/
@[ext] structure Idem (X : C) where
  hom : X ⟶ X
  restriction : rst hom = hom

namespace Idem

variable {X : C}

theorem idem (a : Idem X) : a.hom ≫ a.hom = a.hom := by
  simpa only [a.restriction] using rst_comp_self a.hom

theorem comm (a b : Idem X) : a.hom ≫ b.hom = b.hom ≫ a.hom := by
  simpa only [a.restriction, b.restriction] using rst_comm a.hom b.hom

instance : PartialOrder (Idem X) where
  le a b := a.hom ≫ b.hom = a.hom
  le_refl a := a.idem
  le_trans a b c hab hbc := by
    calc
      _ = (a.hom ≫ b.hom) ≫ c.hom := by rw [hab]
      _ = a.hom := by rw [Category.assoc, hbc, hab]
  le_antisymm a b hab hba := Idem.ext <| by
    calc a.hom = a.hom ≫ b.hom := hab.symm
      _ = b.hom ≫ a.hom := a.comm b
      _ = b.hom := hba

theorem le_def {a b : Idem X} : a ≤ b ↔ a.hom ≫ b.hom = a.hom := Iff.rfl

instance : SemilatticeInf (Idem X) where
  inf a b := ⟨a.hom ≫ b.hom, by
    rw [← a.restriction, rst_comp_rst, b.restriction]⟩
  inf_le_left a b := by
    change (a.hom ≫ b.hom) ≫ a.hom = a.hom ≫ b.hom
    rw [Category.assoc, b.comm a, ← Category.assoc, a.idem]
  inf_le_right a b := by
    change (a.hom ≫ b.hom) ≫ b.hom = a.hom ≫ b.hom
    rw [Category.assoc, b.idem]
  le_inf a b c hab hac := by
    change a.hom ≫ (b.hom ≫ c.hom) = a.hom
    rw [← Category.assoc, hab, hac]

@[simp] theorem inf_hom (a b : Idem X) : (a ⊓ b).hom = a.hom ≫ b.hom := rfl

instance : OrderTop (Idem X) where
  top := ⟨𝟙 X, rst_id X⟩
  le_top a := Category.comp_id a.hom

@[simp] theorem top_hom : (⊤ : Idem X).hom = 𝟙 X := rfl

/-- The restriction idempotent of a morphism. -/
def ofRestrict {Y : C} (f : X ⟶ Y) : Idem X := ⟨rst f, restrict_restrict f⟩

/-- Inverse image along an arbitrary partial morphism. -/
def pull {X Y : C} (f : X ⟶ Y) (a : Idem Y) : Idem X :=
  ofRestrict (f ≫ a.hom)

@[simp] theorem pull_hom {X Y : C} (f : X ⟶ Y) (a : Idem Y) :
    (pull f a).hom = rst (f ≫ a.hom) := rfl

theorem pull_commute {X Y : C} (f : X ⟶ Y) (a : Idem Y) :
    (pull f a).hom ≫ f = f ≫ a.hom := by
  rw [pull_hom, rst_comp, a.restriction]

theorem pull_inf {X Y : C} (f : X ⟶ Y) (a b : Idem Y) :
    pull f (a ⊓ b) = pull f a ⊓ pull f b := by
  apply Idem.ext
  change rst (f ≫ (a.hom ≫ b.hom)) = rst (f ≫ a.hom) ≫ rst (f ≫ b.hom)
  calc
    _ = rst (((pull f a).hom ≫ f) ≫ b.hom) := by rw [pull_commute, Category.assoc]
    _ = _ := by rw [pull_hom, Category.assoc, rst_comp_rst]

theorem pull_mono {X Y : C} (f : X ⟶ Y) : Monotone (pull f) := by
  intro a b hab
  have h := pull_inf f a b
  rw [inf_eq_left.mpr hab] at h
  exact inf_eq_left.mp h.symm

@[simp] theorem pull_id (a : Idem X) : pull (𝟙 X) a = a := by
  apply Idem.ext
  simp only [pull_hom, Category.id_comp, a.restriction]

theorem pull_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (a : Idem Z) :
    pull (f ≫ g) a = pull f (pull g a) := by
  apply Idem.ext
  change rst ((f ≫ g) ≫ a.hom) = rst (f ≫ rst (g ≫ a.hom))
  rw [Category.assoc, ← rst_comp_rst_right]

@[simp] theorem pull_top {X Y : C} (f : X ⟶ Y) : pull f ⊤ = ofRestrict f := by
  apply Idem.ext
  simp only [pull_hom, top_hom, Category.comp_id, ofRestrict]

theorem pull_top_of_total {X Y : C} (f : X ⟶ Y) (hf : isTotal f) : pull f ⊤ = ⊤ :=
  Idem.ext <| by simpa only [pull_hom, top_hom, Category.comp_id] using
    (show rst f = 𝟙 X from hf)

end Idem

/-- The zero morphisms have empty restriction domain. -/
class RestrictionZero (C : Type u) [Category.{v} C] [RestrictionCategory C]
    [HasZeroMorphisms C] : Prop where
  restrict_zero : ∀ X Y : C, rst (0 : X ⟶ Y) = 0

namespace Idem

variable [HasZeroMorphisms C] [RestrictionZero C] {X : C}

instance : OrderBot (Idem X) where
  bot := ⟨0, RestrictionZero.restrict_zero X X⟩
  bot_le _a := zero_comp

@[simp] theorem bot_hom : (⊥ : Idem X).hom = 0 := rfl

@[simp] theorem pull_bot {X Y : C} (f : X ⟶ Y) : pull f ⊥ = ⊥ := by
  apply Idem.ext
  simp only [pull_hom, bot_hom, comp_zero, RestrictionZero.restrict_zero]

end Idem

/-- Complementarity needs only the join of this particular pair: the
identity is its least upper bound. -/
structure PairComplementary [HasZeroMorphisms C] [RestrictionZero C]
    {X : C} (a b : Idem X) : Prop where
  disjoint : a ⊓ b = ⊥
  cover : ∀ d : Idem X, a ≤ d → b ≤ d → (⊤ : Idem X) ≤ d

/-- Binary least upper bounds in the restriction-idempotent order. -/
class BinaryJoins (C : Type u) [Category.{v} C] [RestrictionCategory C] where
  join : {X : C} → Idem X → Idem X → Idem X
  le_left : ∀ {X : C} (a b : Idem X), a ≤ join a b
  le_right : ∀ {X : C} (a b : Idem X), b ≤ join a b
  least : ∀ {X : C} (a b c : Idem X), a ≤ c → b ≤ c → join a b ≤ c

instance [BinaryJoins C] (X : C) : SemilatticeSup (Idem X) where
  sup := BinaryJoins.join
  le_sup_left := BinaryJoins.le_left
  le_sup_right := BinaryJoins.le_right
  sup_le := BinaryJoins.least

/-- Only total inverse images are required to preserve joins. -/
class TotalJoinInverse (C : Type u) [Category.{v} C] [RestrictionCategory C]
    [BinaryJoins C] : Prop where
  pull_sup : ∀ {X Y : C} (f : X ⟶ Y), isTotal f → ∀ a b : Idem Y,
    Idem.pull f (a ⊔ b) = Idem.pull f a ⊔ Idem.pull f b

/-- Join preservation along arbitrary partial morphisms. -/
class JoinInverse (C : Type u) [Category.{v} C] [RestrictionCategory C]
    [BinaryJoins C] : Prop where
  pull_sup : ∀ {X Y : C} (f : X ⟶ Y) (a b : Idem Y),
    Idem.pull f (a ⊔ b) = Idem.pull f a ⊔ Idem.pull f b

instance [BinaryJoins C] [JoinInverse C] : TotalJoinInverse C :=
  ⟨fun f _ => JoinInverse.pull_sup f⟩

variable [HasZeroMorphisms C] [RestrictionZero C] [BinaryJoins C]

/-- A complementary pair is disjoint and covers the identity. -/
structure Complementary {X : C} (a b : Idem X) : Prop where
  disjoint : a ⊓ b = ⊥
  cover : a ⊔ b = ⊤

theorem Complementary.toPair {X : C} {a b : Idem X} (h : Complementary a b) :
    PairComplementary a b := ⟨h.disjoint, fun d ha hb => by
      rw [← h.cover]; exact sup_le ha hb⟩

theorem Complementary.symm {X : C} {a b : Idem X} (h : Complementary a b) :
    Complementary b a := ⟨by rw [inf_comm, h.disjoint], by rw [sup_comm, h.cover]⟩

/-- An inseparable pair includes the disjointness requirement. -/
structure Inseparable {X : C} (a b : Idem X) : Prop where
  disjoint : a ⊓ b = ⊥
  no_separator : ¬ ∃ c c' : Idem X, Complementary c c' ∧ a ≤ c ∧ b ≤ c'

theorem Complementary.pull [TotalJoinInverse C] {X Y : C} {a b : Idem Y}
    (h : Complementary a b) (f : X ⟶ Y) (hf : isTotal f) :
    Complementary (Idem.pull f a) (Idem.pull f b) := by
  constructor
  · rw [← Idem.pull_inf, h.disjoint, Idem.pull_bot]
  · rw [← TotalJoinInverse.pull_sup f hf, h.cover, Idem.pull_top_of_total f hf]

/-- The theorem and refutation domains of a consistent extension remain inseparable. -/
theorem domain_incompleteness [TotalJoinInverse C] {U S : C}
    {a b : Idem U} (hab : Inseparable a b)
    (θ : U ⟶ S) (hθ : isTotal θ) (ν : S ⟶ S) (_hν : isTotal ν)
    (t₀ : Idem S) (ha : a ≤ Idem.pull θ t₀)
    (hb : b ≤ Idem.pull θ (Idem.pull ν t₀))
    (t : Idem S) (ht : t₀ ≤ t) (hconsistent : t ⊓ Idem.pull ν t = ⊥) :
    Inseparable t (Idem.pull ν t) ∧ t ⊔ Idem.pull ν t ≠ ⊤ := by
  have hi : Inseparable t (Idem.pull ν t) := by
    refine ⟨hconsistent, ?_⟩
    rintro ⟨c, c', hc, htc, htc'⟩
    exact hab.no_separator ⟨Idem.pull θ c, Idem.pull θ c', hc.pull θ hθ,
      ha.trans (Idem.pull_mono θ (ht.trans htc)),
      hb.trans (Idem.pull_mono θ ((Idem.pull_mono ν ht).trans htc'))⟩
  refine ⟨hi, ?_⟩
  intro hcomplete
  exact hi.no_separator ⟨t, Idem.pull ν t, ⟨hconsistent, hcomplete⟩, le_rfl, le_rfl⟩

end CategoricalEssentialIncompleteness.LocalConnectedness
