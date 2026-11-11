/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.EffectiveForkInverses

/-! # Finite probes and componentwise injectivity of partial monomorphisms -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork

open EnumerableCarriers (Carrier val)

def emptyCarrier : Carrier := ⟨∅, REPred.const False⟩
def singletonCarrier : Carrier := ⟨{0},
  (Primrec.eq.comp Primrec.id (Primrec.const 0)).computablePred.to_re⟩

theorem zero_empty_total (X : Carrier) : isTotal (0 : emptyCarrier ⟶ X) :=
  (EnumerableCarriers.total_iff _).mpr (fun _ h => False.elim h)

def H0 : Object := ⟨singletonCarrier, singletonCarrier, singletonCarrier,
  𝟙 _, 𝟙 _, rst_id _, rst_id _⟩
def H1 : Object := ⟨emptyCarrier, singletonCarrier, emptyCarrier,
  0, 0, zero_empty_total _, zero_empty_total _⟩
def H2 : Object := ⟨emptyCarrier, emptyCarrier, singletonCarrier,
  0, 0, zero_empty_total _, zero_empty_total _⟩

def constant {X Y : Carrier} (y : ℕ) (hy : y ∈ Y.support) : X ⟶ Y :=
  EnumerableCarriers.totalFromFunction (fun _ => y) (.const y) (fun _ _ => hy)

theorem constant_total {X Y : Carrier} (y : ℕ) (hy : y ∈ Y.support) :
    isTotal (constant (X := X) y hy) :=
  EnumerableCarriers.totalFromFunction_total (fun _ => y) (.const y) (fun _ _ => hy)

theorem val_constant_at {X Y : Carrier} (y : ℕ) (hy : y ∈ Y.support)
    (x : ℕ) (hx : x ∈ X.support) : val (constant y hy : X ⟶ Y) x = Part.some y :=
  Part.eq_some_iff.mpr ((EnumerableCarriers.mem_totalFromFunction _ _ _ x y).mpr ⟨hx, rfl⟩)

theorem respects_constant {C A : Carrier} (r : C ⟶ A)
    (x u : ℕ) (hx : x ∈ C.support) (hu : u ∈ val r x) :
    Respects (𝟙 singletonCarrier) r (constant x hx)
      (constant u (EnumerableCarriers.val_target r x u hu)) := by
  intro z y w v hzy hzw hyv
  obtain ⟨hz, hey⟩ := (EnumerableCarriers.mem_totalFromFunction _ _ _ z y).mp hzy
  obtain ⟨_, hew⟩ := (mem_supportIdentity singletonCarrier.support z w).mp hzw
  subst y
  subst w
  exact (EnumerableCarriers.mem_totalFromFunction _ _ _ z v).mpr
    ⟨hz, Part.mem_unique hyv hu⟩

def point0 {X : Object} (x u v : ℕ) (hx : x ∈ X.center.support)
    (hu : u ∈ val X.leftMap x) (hv : v ∈ val X.rightMap x) : H0 ⟶ X :=
  ⟨constant x hx, constant u (EnumerableCarriers.val_target _ _ _ hu),
    constant v (EnumerableCarriers.val_target _ _ _ hv),
    respects_constant _ x u hx hu, respects_constant _ x v hx hv⟩

def point1 {X : Object} (u : ℕ) (hu : u ∈ X.left.support) : H1 ⟶ X :=
  ⟨0, constant u hu, 0,
    fun _ _ _ _ h _ _ => False.elim (Part.notMem_none _ h),
    fun _ _ _ _ h _ _ => False.elim (Part.notMem_none _ h)⟩

def point2 {X : Object} (v : ℕ) (hv : v ∈ X.right.support) : H2 ⟶ X :=
  ⟨0, 0, constant v hv,
    fun _ _ _ _ h _ _ => False.elim (Part.notMem_none _ h),
    fun _ _ _ _ h _ _ => False.elim (Part.notMem_none _ h)⟩

theorem point0_total {X : Object} (x u v : ℕ) (hx : x ∈ X.center.support)
    (hu : u ∈ val X.leftMap x) (hv : v ∈ val X.rightMap x) : isTotal (point0 x u v hx hu hv) :=
  (total_iff _).mpr ⟨constant_total x hx,
    constant_total u (EnumerableCarriers.val_target _ _ _ hu),
    constant_total v (EnumerableCarriers.val_target _ _ _ hv)⟩

theorem point1_total {X : Object} (u : ℕ) (hu : u ∈ X.left.support) : isTotal (point1 u hu) :=
  (total_iff _).mpr ⟨zero_empty_total _, constant_total u hu, zero_empty_total _⟩

theorem point2_total {X : Object} (v : ℕ) (hv : v ∈ X.right.support) : isTotal (point2 v hv) :=
  (total_iff _).mpr ⟨zero_empty_total _, zero_empty_total _, constant_total v hv⟩

theorem constant_comp_eq {W X Y : Carrier} (f : X ⟶ Y) (x x' y : ℕ)
    (hx : x ∈ X.support) (hx' : x' ∈ X.support)
    (hf : y ∈ val f x) (hf' : y ∈ val f x') :
    (constant x hx : W ⟶ X) ≫ f = constant x' hx' ≫ f := by
  apply EnumerableCarriers.val_ext_on_source
  intro n hn
  rw [EnumerableCarriers.val_comp, EnumerableCarriers.val_comp,
    val_constant_at _ _ _ hn, val_constant_at _ _ _ hn, Part.bind_some, Part.bind_some]
  exact (Part.eq_some_iff.mpr hf).trans (Part.eq_some_iff.mpr hf').symm

theorem constant_restriction_injective {W X Y : Carrier} (f : X ⟶ Y) (x x' : ℕ)
    (hx : x ∈ X.support) (hx' : x' ∈ X.support)
    (hd : (val f x).Dom) (hd' : (val f x').Dom) (n : ℕ) (hn : n ∈ W.support)
    (he : (constant x hx : W ⟶ X) ≫ rst f = constant x' hx' ≫ rst f) : x=x' := by
  have h0 : val (rst f) x = Part.some x := Part.eq_some_iff.mpr
    ((EnumerableCarriers.mem_val_restriction f x x).mpr ⟨Part.dom_iff_mem.mp hd, rfl⟩)
  have h1 : val (rst f) x' = Part.some x' := Part.eq_some_iff.mpr
    ((EnumerableCarriers.mem_val_restriction f x' x').mpr ⟨Part.dom_iff_mem.mp hd', rfl⟩)
  have hh := congrArg (fun k => val k n) he
  rw [EnumerableCarriers.val_comp, EnumerableCarriers.val_comp,
    val_constant_at _ _ _ hn, val_constant_at _ _ _ hn, Part.bind_some, Part.bind_some,
    h0, h1] at hh
  exact Part.some_injective hh

theorem point0_comp_eq {X Y : Object} (f : X ⟶ Y) (x x' y u u' v v' : ℕ)
    (hx : x ∈ X.center.support) (hx' : x' ∈ X.center.support)
    (hu : u ∈ val X.leftMap x) (hu' : u' ∈ val X.leftMap x')
    (hv : v ∈ val X.rightMap x) (hv' : v' ∈ val X.rightMap x')
    (hf : y ∈ val f.center x) (hf' : y ∈ val f.center x') :
    point0 x u v hx hu hv ≫ f = point0 x' u' v' hx' hu' hv' ≫ f := by
  have hy := EnumerableCarriers.val_target f.center x y hf
  obtain ⟨a, ha⟩ := Part.dom_iff_mem.mp
    ((EnumerableCarriers.total_iff Y.leftMap).mp Y.left_total y hy)
  obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp
    ((EnumerableCarriers.total_iff Y.rightMap).mp Y.right_total y hy)
  exact Hom.ext (constant_comp_eq f.center x x' y hx hx' hf hf')
    (constant_comp_eq f.left u u' a (EnumerableCarriers.val_target _ _ _ hu)
      (EnumerableCarriers.val_target _ _ _ hu') (f.natural_left x y u a hf hu ha)
      (f.natural_left x' y u' a hf' hu' ha))
    (constant_comp_eq f.right v v' b (EnumerableCarriers.val_target _ _ _ hv)
      (EnumerableCarriers.val_target _ _ _ hv') (f.natural_right x y v b hf hv hb)
      (f.natural_right x' y v' b hf' hv' hb))

theorem injective_of_partialMono {X Y : Object} (f : X ⟶ Y) (hf : PartialMono f) :
    Injective f := by
  refine ⟨?_, ?_, ?_⟩
  · intro x x' y hxy hx'y
    have hx := EnumerableCarriers.val_source f.center x y hxy
    have hx' := EnumerableCarriers.val_source f.center x' y hx'y
    obtain ⟨u, hu⟩ := Part.dom_iff_mem.mp
      ((EnumerableCarriers.total_iff X.leftMap).mp X.left_total x hx)
    obtain ⟨u', hu'⟩ := Part.dom_iff_mem.mp
      ((EnumerableCarriers.total_iff X.leftMap).mp X.left_total x' hx')
    obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp
      ((EnumerableCarriers.total_iff X.rightMap).mp X.right_total x hx)
    obtain ⟨v', hv'⟩ := Part.dom_iff_mem.mp
      ((EnumerableCarriers.total_iff X.rightMap).mp X.right_total x' hx')
    have he := hf (point0 x u v hx hu hv) (point0 x' u' v' hx' hu' hv')
      (point0_comp_eq f x x' y u u' v v' hx hx' hu hu' hv hv' hxy hx'y)
    exact constant_restriction_injective (W := singletonCarrier)
      f.center x x' hx hx' hxy.1 hx'y.1 0 rfl
      (congrArg Hom.center he)
  · intro u u' y huy hu'y
    have hu := EnumerableCarriers.val_source f.left u y huy
    have hu' := EnumerableCarriers.val_source f.left u' y hu'y
    have he : point1 u hu ≫ f = point1 u' hu' ≫ f := Hom.ext
      rfl (constant_comp_eq f.left u u' y hu hu' huy hu'y) rfl
    exact constant_restriction_injective (W := singletonCarrier)
      f.left u u' hu hu' huy.1 hu'y.1 0 rfl
      (congrArg Hom.left (hf _ _ he))
  · intro v v' y hvy hv'y
    have hv := EnumerableCarriers.val_source f.right v y hvy
    have hv' := EnumerableCarriers.val_source f.right v' y hv'y
    have he : point2 v hv ≫ f = point2 v' hv' ≫ f := Hom.ext
      rfl rfl (constant_comp_eq f.right v v' y hv hv' hvy hv'y)
    exact constant_restriction_injective (W := singletonCarrier)
      f.right v v' hv hv' hvy.1 hv'y.1 0 rfl
      (congrArg Hom.right (hf _ _ he))

theorem partialMono_iff_injective {X Y : Object} (f : X ⟶ Y) :
    PartialMono f ↔ Injective f := ⟨injective_of_partialMono f, partialMono_of_injective f⟩

instance : WeakChoice Object where
  section_exists f hf := section_of_injective f (injective_of_partialMono f hf)

end CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork
