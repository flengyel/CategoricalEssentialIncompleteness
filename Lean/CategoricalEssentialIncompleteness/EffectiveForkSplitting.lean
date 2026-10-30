/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.EffectiveForkConnected

/-! # Splitting through the c.e. domain subfunctor -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork

open EnumerableCarriers (Carrier val)

def domainObject {X : Object} (a : Idem X) : Object where
  center := EnumerableCarriers.subcarrier (centerIdem a)
  left := EnumerableCarriers.subcarrier (leftIdem a)
  right := EnumerableCarriers.subcarrier (rightIdem a)
  leftMap := EnumerableCarriers.restrictMap X.leftMap (centerIdem a) (leftIdem a) (closed_left a)
  rightMap := EnumerableCarriers.restrictMap X.rightMap (centerIdem a) (rightIdem a)
    (closed_right a)
  left_total := EnumerableCarriers.restrictMap_total _ X.left_total _ _ (closed_left a)
  right_total := EnumerableCarriers.restrictMap_total _ X.right_total _ _ (closed_right a)

theorem respects_into {C A : Carrier} (r : C ⟶ A) (a : Idem C) (b : Idem A)
    (h : Closed r a b) :
    Respects (EnumerableCarriers.restrictMap r a b h) r
      (EnumerableCarriers.into a) (EnumerableCarriers.into b) := by
  intro x y u v hxy hxu hyv
  obtain ⟨hx, he⟩ := (EnumerableCarriers.mem_val_idem a x y).mp hxy
  subst y
  obtain ⟨_, hru⟩ := (EnumerableCarriers.mem_val_restrictMap r a b h x u).mp hxu
  exact (EnumerableCarriers.mem_val_idem b u v).mpr ⟨h x u hx hru,
    Part.mem_unique hyv hru⟩

theorem respects_outof {C A : Carrier} (r : C ⟶ A) (a : Idem C) (b : Idem A)
    (h : Closed r a b) :
    Respects r (EnumerableCarriers.restrictMap r a b h)
      (EnumerableCarriers.outof a) (EnumerableCarriers.outof b) := by
  intro x y u v hxy hxu hyv
  obtain ⟨hx, he⟩ := (EnumerableCarriers.mem_val_idem a x y).mp hxy
  subst y
  obtain ⟨_, hrv⟩ := (EnumerableCarriers.mem_val_restrictMap r a b h x v).mp hyv
  exact (EnumerableCarriers.mem_val_idem b u v).mpr ⟨h x u hx hxu,
    Part.mem_unique hrv hxu⟩

def domainInclusion {X : Object} (a : Idem X) : domainObject a ⟶ X :=
  ⟨EnumerableCarriers.into (centerIdem a), EnumerableCarriers.into (leftIdem a),
    EnumerableCarriers.into (rightIdem a), respects_into _ _ _ (closed_left a),
    respects_into _ _ _ (closed_right a)⟩

def domainRetraction {X : Object} (a : Idem X) : X ⟶ domainObject a :=
  ⟨EnumerableCarriers.outof (centerIdem a), EnumerableCarriers.outof (leftIdem a),
    EnumerableCarriers.outof (rightIdem a), respects_outof _ _ _ (closed_left a),
    respects_outof _ _ _ (closed_right a)⟩

theorem domainInclusion_total {X : Object} (a : Idem X) : isTotal (domainInclusion a) :=
  (total_iff _).mpr ⟨EnumerableCarriers.into_total _, EnumerableCarriers.into_total _,
    EnumerableCarriers.into_total _⟩

theorem inclusion_retraction {X : Object} (a : Idem X) :
    domainInclusion a ≫ domainRetraction a = 𝟙 (domainObject a) :=
  Hom.ext (EnumerableCarriers.into_outof _) (EnumerableCarriers.into_outof _)
    (EnumerableCarriers.into_outof _)

theorem retraction_inclusion {X : Object} (a : Idem X) :
    domainRetraction a ≫ domainInclusion a = a.hom :=
  Hom.ext (EnumerableCarriers.outof_into _) (EnumerableCarriers.outof_into _)
    (EnumerableCarriers.outof_into _)

instance : Splits Object where
  splitting a := ⟨domainObject a, domainInclusion a, domainRetraction a,
    domainInclusion_total a, inclusion_retraction a, retraction_inclusion a⟩

end CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork
