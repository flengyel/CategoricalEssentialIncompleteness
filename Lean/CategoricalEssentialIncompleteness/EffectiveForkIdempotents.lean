/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.EffectiveFork

/-! # Effective subfunctors, ranges and inverse images on the fork -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork

open EnumerableCarriers (Carrier val)

def centerIdem {X : Object} (a : Idem X) : Idem X.center :=
  ⟨a.hom.center, congrArg Hom.center a.restriction⟩
def leftIdem {X : Object} (a : Idem X) : Idem X.left :=
  ⟨a.hom.left, congrArg Hom.left a.restriction⟩
def rightIdem {X : Object} (a : Idem X) : Idem X.right :=
  ⟨a.hom.right, congrArg Hom.right a.restriction⟩

theorem idem_ext {X : Object} {a b : Idem X}
    (hc : centerIdem a = centerIdem b) (hl : leftIdem a = leftIdem b)
    (hr : rightIdem a = rightIdem b) : a = b :=
  Idem.ext (Hom.ext (congrArg Idem.hom hc) (congrArg Idem.hom hl) (congrArg Idem.hom hr))

theorem idem_le_iff {X : Object} (a b : Idem X) :
    a ≤ b ↔ centerIdem a ≤ centerIdem b ∧ leftIdem a ≤ leftIdem b ∧
      rightIdem a ≤ rightIdem b := by
  constructor
  · intro h
    exact ⟨congrArg Hom.center h, congrArg Hom.left h, congrArg Hom.right h⟩
  · rintro ⟨hc, hl, hr⟩
    exact Hom.ext hc hl hr

def Closed {C A : Carrier} (r : C ⟶ A) (a : Idem C) (b : Idem A) : Prop :=
  ∀ x u, x ∈ EnumerableCarriers.support a → u ∈ val r x →
    u ∈ EnumerableCarriers.support b

theorem closed_left {X : Object} (a : Idem X) :
    Closed X.leftMap (centerIdem a) (leftIdem a) := by
  intro x u hx hu
  have hh := a.hom.natural_left x x u u
    ((EnumerableCarriers.mem_val_idem (centerIdem a) x x).mpr ⟨hx, rfl⟩) hu hu
  exact ((EnumerableCarriers.mem_val_idem (leftIdem a) u u).mp hh).1

theorem closed_right {X : Object} (a : Idem X) :
    Closed X.rightMap (centerIdem a) (rightIdem a) := by
  intro x u hx hu
  have hh := a.hom.natural_right x x u u
    ((EnumerableCarriers.mem_val_idem (centerIdem a) x x).mpr ⟨hx, rfl⟩) hu hu
  exact ((EnumerableCarriers.mem_val_idem (rightIdem a) u u).mp hh).1

theorem respects_idem {C A : Carrier} {r : C ⟶ A} {a : Idem C} {b : Idem A}
    (h : Closed r a b) : Respects r r a.hom b.hom := by
  intro x y u v hxy hxu hyv
  obtain ⟨hx, he⟩ := (EnumerableCarriers.mem_val_idem a x y).mp hxy
  subst y
  exact (EnumerableCarriers.mem_val_idem b u v).mpr ⟨h x u hx hxu,
    Part.mem_unique hyv hxu⟩

def identityOn {X : Object} (a : Idem X.center) (b : Idem X.left) (c : Idem X.right)
    (hl : Closed X.leftMap a b) (hr : Closed X.rightMap a c) : Idem X :=
  ⟨⟨a.hom, b.hom, c.hom, respects_idem hl, respects_idem hr⟩,
    Hom.ext a.restriction b.restriction c.restriction⟩

theorem closed_sup {C A : Carrier} {r : C ⟶ A} {a a' : Idem C} {b b' : Idem A}
    (h : Closed r a b) (h' : Closed r a' b') : Closed r (a ⊔ a') (b ⊔ b') := by
  intro x u hx hu
  rw [EnumerableCarriers.support_sup] at hx ⊢
  exact hx.elim (fun hx => Or.inl (h x u hx hu)) (fun hx => Or.inr (h' x u hx hu))

instance : BinaryJoins Object where
  join a b := identityOn (centerIdem a ⊔ centerIdem b) (leftIdem a ⊔ leftIdem b)
    (rightIdem a ⊔ rightIdem b) (closed_sup (closed_left a) (closed_left b))
    (closed_sup (closed_right a) (closed_right b))
  le_left a b := (idem_le_iff _ _).mpr ⟨le_sup_left, le_sup_left, le_sup_left⟩
  le_right a b := (idem_le_iff _ _).mpr ⟨le_sup_right, le_sup_right, le_sup_right⟩
  least a b c ha hb := by
    obtain ⟨hac, hal, har⟩ := (idem_le_iff a c).mp ha
    obtain ⟨hbc, hbl, hbr⟩ := (idem_le_iff b c).mp hb
    exact (idem_le_iff _ _).mpr ⟨sup_le hac hbc, sup_le hal hbl, sup_le har hbr⟩

instance : JoinInverse Object where
  pull_sup f a b := idem_ext
    (JoinInverse.pull_sup f.center (centerIdem a) (centerIdem b))
    (JoinInverse.pull_sup f.left (leftIdem a) (leftIdem b))
    (JoinInverse.pull_sup f.right (rightIdem a) (rightIdem b))

theorem closed_range {C A D B : Carrier} {r : C ⟶ A} {s : D ⟶ B}
    {f : C ⟶ D} {g : A ⟶ B} (rt : isTotal r) (hf : Respects r s f g) :
    Closed s (Ranges.range f) (Ranges.range g) := by
  intro y v hy hv
  rw [EnumerableCarriers.support_range] at hy ⊢
  obtain ⟨x, hxy⟩ := hy
  have hd := (EnumerableCarriers.total_iff r).mp rt x
    (EnumerableCarriers.val_source f x y hxy)
  obtain ⟨u, hu⟩ := Part.dom_iff_mem.mp hd
  exact ⟨u, hf x y u v hxy hu hv⟩

instance : Ranges Object where
  range {X Y} f := identityOn (Ranges.range f.center) (Ranges.range f.left)
    (Ranges.range f.right) (closed_range X.left_total f.natural_left)
    (closed_range X.right_total f.natural_right)
  receives f := Hom.ext (Ranges.receives f.center) (Ranges.receives f.left)
    (Ranges.receives f.right)
  agreement f g h he := Hom.ext
    (Ranges.agreement f.center g.center h.center (congrArg Hom.center he))
    (Ranges.agreement f.left g.left h.left (congrArg Hom.left he))
    (Ranges.agreement f.right g.right h.right (congrArg Hom.right he))

end CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork
