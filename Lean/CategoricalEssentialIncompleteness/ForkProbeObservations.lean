/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.EffectiveForkEvaluation
public import CategoricalEssentialIncompleteness.EffectiveForkProbes
public import CategoricalEssentialIncompleteness.EnumerableFreeSemigroup

/-! # Endpoint probes and their actual partial observation functors -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness

namespace EnumerableCarriers

def supportedFunction {X Y : Carrier} (f : X ⟶ Y) (x : Element X) : Part (Element Y) :=
  ⟨(val f x.val).Dom,fun h => ⟨(val f x.val).get h,val_target f _ _ (Part.get_mem h)⟩⟩

theorem mem_supportedFunction {X Y : Carrier} (f : X ⟶ Y) (x : Element X) (y : Element Y) :
    y ∈ supportedFunction f x ↔ y.val ∈ val f x.val := by
  change (∃ h : (val f x.val).Dom,
    (⟨(val f x.val).get h,val_target f _ _ (Part.get_mem h)⟩ : Element Y)=y) ↔ _
  constructor
  · rintro ⟨h,he⟩
    exact congrArg Subtype.val he ▸ Part.get_mem h
  · intro hy
    exact ⟨hy.1,Subtype.ext hy.2⟩

def partialUnderlying : Carrier ⥤ PartialFunctions.Pfn where
  obj X := PartialFun.of (Element X)
  map := supportedFunction
  map_id X := by
    apply PFun.ext
    intro x y
    rw [mem_supportedFunction,val_id,mem_supportIdentity]
    change (x.val ∈ X.support ∧ y.val=x.val) ↔ y ∈ Part.some x
    simp only [x.property,true_and,Part.mem_some_iff,Subtype.ext_iff]
  map_comp {X Y Z} f g := by
    apply PFun.ext
    intro x z
    rw [mem_supportedFunction,val_comp,Part.mem_bind_iff]
    change (∃ y : ℕ,y ∈ val f x.val ∧ z.val ∈ val g y) ↔
      z ∈ (supportedFunction f x).bind (supportedFunction g)
    rw [Part.mem_bind_iff]
    simp only [mem_supportedFunction]
    constructor
    · rintro ⟨y,hy,hz⟩
      exact ⟨⟨y,val_target f _ _ hy⟩,hy,hz⟩
    · rintro ⟨y,hy,hz⟩
      exact ⟨y.val,hy,hz⟩

end EnumerableCarriers

namespace EffectiveFork

open EnumerableCarriers (Carrier val Element)

def endpoint (i : Bool) : Component := if i then .right else .left
def endpointProbe (i : Bool) : Object := if i then H2 else H1
abbrev ProbeTotal (i : Bool) (Y : Object) := {p : endpointProbe i ⟶ Y // isTotal p}

def probePoint {Y : Object} : (i : Bool) → Element ((evaluation (endpoint i)).obj Y) → ProbeTotal i Y
  | false,y => ⟨point1 y.val y.property,point1_total y.val y.property⟩
  | true,y => ⟨point2 y.val y.property,point2_total y.val y.property⟩

def probeValue {Y : Object} : (i : Bool) → ProbeTotal i Y → Element ((evaluation (endpoint i)).obj Y)
  | false,p => EnumerableCarriers.typedMap p.val.left ((total_iff p.val).mp p.property).2.1
      ⟨0,by rfl⟩
  | true,p => EnumerableCarriers.typedMap p.val.right ((total_iff p.val).mp p.property).2.2
      ⟨0,by rfl⟩

theorem probeValue_mem {Y : Object} (i : Bool) (p : ProbeTotal i Y) :
    (probeValue i p).val ∈ val ((evaluation (endpoint i)).map p.val) 0 := by
  cases i
  · exact EnumerableCarriers.typedMap_mem p.val.left ((total_iff p.val).mp p.property).2.1
      (⟨0,by rfl⟩ : Element singletonCarrier)
  · exact EnumerableCarriers.typedMap_mem p.val.right ((total_iff p.val).mp p.property).2.2
      (⟨0,by rfl⟩ : Element singletonCarrier)

theorem empty_arrow_zero {X : Carrier} (f : emptyCarrier ⟶ X) : f=0 := by
  apply EnumerableCarriers.val_ext_on_source
  intro n hn
  exact False.elim hn

theorem singleton_arrow_constant {X : Carrier} (f : singletonCarrier ⟶ X)
    (y : ℕ) (hy : y ∈ val f 0) : f=constant y (EnumerableCarriers.val_target f _ _ hy) := by
  apply EnumerableCarriers.val_ext_on_source
  intro n hn
  have he : n=0 := Set.mem_singleton_iff.mp hn
  subst n
  exact (Part.eq_some_iff.mpr hy).trans (val_constant_at _ _ _ (by rfl)).symm

theorem probePoint_value {Y : Object} (i : Bool) (p : ProbeTotal i Y) :
    probePoint i (probeValue i p)=p := by
  apply Subtype.ext
  cases i
  · exact Hom.ext (empty_arrow_zero p.val.center).symm
      (singleton_arrow_constant p.val.left _ (probeValue_mem false p)).symm
      (empty_arrow_zero p.val.right).symm
  · exact Hom.ext (empty_arrow_zero p.val.center).symm
      (empty_arrow_zero p.val.left).symm
      (singleton_arrow_constant p.val.right _ (probeValue_mem true p)).symm

theorem probeValue_point {Y : Object} (i : Bool) (y : Element ((evaluation (endpoint i)).obj Y)) :
    probeValue i (probePoint i y)=y := by
  apply Subtype.ext
  cases i
  all_goals
    exact Part.mem_unique (probeValue_mem _ _)
      (Part.eq_some_iff.mp (val_constant_at y.val y.property 0 (by rfl)))

def probeEquiv (i : Bool) (Y : Object) : ProbeTotal i Y ≃ Element ((evaluation (endpoint i)).obj Y) where
  toFun := probeValue i
  invFun := probePoint i
  left_inv := probePoint_value i
  right_inv := probeValue_point i

end EffectiveFork
end CategoricalEssentialIncompleteness.LocalConnectedness
