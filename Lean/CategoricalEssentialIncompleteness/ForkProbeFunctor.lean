/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.ForkProbeObservations

/-! # The partial functor on total endpoint probes -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork

open EnumerableCarriers (Carrier val Element)

def endpointUnderlying (i : Bool) : Object ⥤ PartialFunctions.Pfn :=
  evaluation (endpoint i) ⋙ EnumerableCarriers.partialUnderlying

def probeIso (i : Bool) (Y : Object) : PartialFun.of (ProbeTotal i Y) ≅ (endpointUnderlying i).obj Y :=
  PartialFun.Iso.mk (α := PartialFun.of (ProbeTotal i Y))
    (β := (endpointUnderlying i).obj Y) (probeEquiv i Y)

def probeFunctor (i : Bool) : Object ⥤ PartialFunctions.Pfn where
  obj Y := PartialFun.of (ProbeTotal i Y)
  map {X Y} f := (probeIso i X).hom ≫
    (endpointUnderlying i).map f ≫ (probeIso i Y).inv
  map_id X := by
    rw [CategoryTheory.Functor.map_id,Category.id_comp]
    exact (probeIso i X).hom_inv_id
  map_comp {X Y Z} f g := by
    rw [CategoryTheory.Functor.map_comp]
    simp only [Category.assoc,Iso.inv_hom_id_assoc]

def probeObservationIso (i : Bool) : probeFunctor i ≅ endpointUnderlying i :=
  NatIso.ofComponents (fun Y => probeIso i Y) (by
    intro X Y f
    change ((probeIso i X).hom ≫
      (endpointUnderlying i).map f ≫ (probeIso i Y).inv) ≫
        (probeIso i Y).hom =
      (probeIso i X).hom ≫ (endpointUnderlying i).map f
    simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id])

theorem probeFunctor_map_value (i : Bool) {X Y : Object} (f : X ⟶ Y) (p : ProbeTotal i X) :
    (probeFunctor i).map f p=
      (EnumerableCarriers.supportedFunction ((evaluation (endpoint i)).map f) (probeValue i p)).map
        (probePoint i) := by
  change (Part.some (probeValue i p)).bind (fun x =>
    (EnumerableCarriers.supportedFunction ((evaluation (endpoint i)).map f) x).bind
      (fun y => Part.some (probePoint i y)))=_
  rw [Part.bind_some,Part.bind_some_eq_map]

theorem mem_probeFunctor (i : Bool) {X Y : Object} (f : X ⟶ Y)
    (p : ProbeTotal i X) (q : ProbeTotal i Y) :
    q ∈ (probeFunctor i).map f p ↔
      (probeValue i q).val ∈ val ((evaluation (endpoint i)).map f) (probeValue i p).val := by
  rw [probeFunctor_map_value,Part.mem_map_iff]
  constructor
  · rintro ⟨y,hy,hq⟩
    have he : y=probeValue i q := by
      have h := congrArg (probeValue i) hq
      simpa only [probeValue_point] using h
    rw [← he]
    exact (EnumerableCarriers.mem_supportedFunction _ _ _).mp hy
  · intro hy
    exact ⟨probeValue i q,(EnumerableCarriers.mem_supportedFunction _ _ _).mpr hy,
      probePoint_value i q⟩

end CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork
