/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PartialMaps
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono

/-! # Functors on monic partial maps induced by pullback-preserving functors -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.V46.PartialMaps

variable {D : Type u₁} [Category.{v₁} D] [HasPullbacks D]
variable {E : Type u₂} [Category.{v₂} E] [HasPullbacks E]
variable (F : D ⥤ E) [F.PreservesMonomorphisms]

def objectMap (X : Par D) : Par E := ⟨F.obj X.obj⟩

def rawMap {X Y : Par D} (s : Raw X Y) : Raw (objectMap F X) (objectMap F Y) :=
  ⟨F.obj s.apex, F.map s.l, F.map s.r, by infer_instance, by trivial⟩

def rawMapIso {X Y : Par D} {s t : Raw X Y} (i : s ≅ t) :
    rawMap F s ≅ rawMap F t :=
  CategoryTheory.Span.mkIso (F.mapIso (CategoryTheory.Span.SpanBicat.apexIso i))
    (by
      change F.map i.hom.hom ≫ F.map t.l = F.map s.l
      simpa only [Functor.map_comp] using congrArg F.map i.hom.hom_l)
    (by
      change F.map i.hom.hom ≫ F.map t.r = F.map s.r
      simpa only [Functor.map_comp] using congrArg F.map i.hom.hom_r)

def homMap {X Y : Par D} : (X ⟶ Y) → (objectMap F X ⟶ objectMap F Y) :=
  Quotient.map (rawMap F) (by
    intro s t h
    obtain ⟨i⟩ := h
    exact ⟨rawMapIso F i⟩)

@[simp] theorem homMap_ofSpan {X Y : Par D} (s : Raw X Y) :
    homMap F (ofSpan s) = ofSpan (rawMap F s) := rfl

def rawMapIdIso (X : Par D) :
    rawMap F (𝟙 (toSpanObject X)) ≅ 𝟙 (toSpanObject (objectMap F X)) :=
  CategoryTheory.Span.mkIso (Iso.refl _)
    (by simp [rawMap]) (by simp [rawMap])

variable [PreservesLimitsOfShape WalkingCospan F]

def rawMapCompIso {X Y Z : Par D} (s : Raw X Y) (t : Raw Y Z) :
    rawMap F (s ≫ t) ≅ rawMap F s ≫ rawMap F t := by
  refine CategoryTheory.Span.mkIso (PreservesPullback.iso F s.r t.l) ?_ ?_
  · change (PreservesPullback.iso F s.r t.l).hom ≫
      (pullback.fst (F.map s.r) (F.map t.l) ≫ F.map s.l) =
        F.map (pullback.fst s.r t.l ≫ s.l)
    rw [← Category.assoc, PreservesPullback.iso_hom_fst, F.map_comp]
  · change (PreservesPullback.iso F s.r t.l).hom ≫
      (pullback.snd (F.map s.r) (F.map t.l) ≫ F.map t.r) =
        F.map (pullback.snd s.r t.l ≫ t.r)
    rw [← Category.assoc, PreservesPullback.iso_hom_snd, F.map_comp]

omit [PreservesLimitsOfShape WalkingCospan F] in
theorem homMap_id (X : Par D) : homMap F (𝟙 X) = 𝟙 (objectMap F X) :=
  ofSpan_eq_of_iso (rawMapIdIso F X)

theorem homMap_comp {X Y Z : Par D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    homMap F (f ≫ g) = homMap F f ≫ homMap F g := by
  induction f using Quotient.inductionOn with | _ s =>
    induction g using Quotient.inductionOn with | _ t =>
      exact ofSpan_eq_of_iso (rawMapCompIso F s t)

def inducedFunctor : Par D ⥤ Par E where
  obj := objectMap F
  map := homMap F
  map_id := homMap_id F
  map_comp := homMap_comp F

theorem inducedFunctor_restriction {X Y : Par D} (f : X ⟶ Y) :
    (inducedFunctor F).map (rst f) = rst ((inducedFunctor F).map f) := by
  induction f using Quotient.inductionOn with | _ s =>
    apply ofSpan_eq_of_iso
    exact CategoryTheory.Span.mkIso (Iso.refl _) (by simp [rawMap, Raw.restriction])
      (by simp [rawMap, Raw.restriction])

theorem inducedFunctor_total {X Y : Par D} (f : X ⟶ Y) (hf : isTotal f) :
    isTotal ((inducedFunctor F).map f) := by
  change rst ((inducedFunctor F).map f) = 𝟙 _
  rw [← inducedFunctor_restriction, hf]
  exact (inducedFunctor F).map_id X

theorem inducedFunctor_ofTotal {X Y : Par D} (f : X.obj ⟶ Y.obj) :
    (inducedFunctor F).map (ofTotal f) = ofTotal (F.map f) := by
  apply ofSpan_eq_of_iso
  exact CategoryTheory.Span.mkIso (Iso.refl _)
    (by simp [rawMap, Raw.total]) (by simp [rawMap, Raw.total])

theorem inducedFunctor_inverseMono {X Y : Par D} (m : X.obj ⟶ Y.obj) [Mono m] :
    (inducedFunctor F).map (inverseMono m) = inverseMono (F.map m) := by
  apply ofSpan_eq_of_iso
  exact CategoryTheory.Span.mkIso (Iso.refl _)
    (by simp [rawMap, Raw.monoInverse]) (by simp [rawMap, Raw.monoInverse])

end CategoricalEssentialIncompleteness.V46.PartialMaps
