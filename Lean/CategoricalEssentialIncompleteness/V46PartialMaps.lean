/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import Mathlib.CategoryTheory.Bicategory.Span.Basic
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.RegularCategory.Basic
public import CategoricalEssentialIncompleteness.RestrictionRanges
public import CategoricalEssentialIncompleteness.LocalSwitch

/-! # Partial maps in an arbitrary category with pullbacks -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoryTheory.Bicategory

namespace CategoricalEssentialIncompleteness.V46.PartialMaps

variable {D : Type u} [Category.{v} D] [HasPullbacks D]

/-- Objects of the partial-map category retain their underlying objects. -/
structure Par (D : Type u) where
  obj : D

abbrev SpanCategory (D : Type u) [Category.{v} D] :=
  CategoryTheory.Span.SpanBicat D (MorphismProperty.monomorphisms D) ⊤

def toSpanObject (X : Par D) : SpanCategory D := ⟨X.obj⟩

/-- A representative is a span with monic left leg. -/
abbrev Raw (X Y : Par D) := toSpanObject X ⟶ toSpanObject Y

instance raw_left_mono {X Y : Par D} (s : Raw X Y) : Mono s.l := s.wl

def spanSetoid (X Y : Par D) : Setoid (Raw X Y) := isIsomorphicSetoid _

def homComp {X Y Z : Par D} :
    Quotient (spanSetoid X Y) → Quotient (spanSetoid Y Z) →
      Quotient (spanSetoid X Z) :=
  Quotient.map₂ (fun s t => s ≫ t) (by
    intro s s' hs t t' ht
    obtain ⟨i⟩ := hs
    obtain ⟨j⟩ := ht
    exact ⟨whiskerRightIso i t ≪≫ whiskerLeftIso s' j⟩)

instance parCategory : Category.{max u v} (Par D) where
  Hom X Y := Quotient (spanSetoid X Y)
  id X := Quotient.mk _ (𝟙 (toSpanObject X))
  comp := homComp
  id_comp f := by
    induction f using Quotient.inductionOn with | _ s =>
      exact Quotient.sound ⟨λ_ s⟩
  comp_id f := by
    induction f using Quotient.inductionOn with | _ s =>
      exact Quotient.sound ⟨ρ_ s⟩
  assoc f g h := by
    induction f using Quotient.inductionOn with | _ s =>
      induction g using Quotient.inductionOn with | _ t =>
        induction h using Quotient.inductionOn with | _ w =>
          exact Quotient.sound ⟨α_ s t w⟩

def ofSpan {X Y : Par D} (s : Raw X Y) : X ⟶ Y := Quotient.mk _ s

@[simp] theorem ofSpan_comp {X Y Z : Par D} (s : Raw X Y) (t : Raw Y Z) :
    ofSpan (s ≫ t) = ofSpan s ≫ ofSpan t := rfl

theorem ofSpan_eq_of_iso {X Y : Par D} {s t : Raw X Y} (i : s ≅ t) :
    ofSpan s = ofSpan t := Quotient.sound ⟨i⟩

theorem ofSpan_eq_iff {X Y : Par D} (s t : Raw X Y) :
    ofSpan s = ofSpan t ↔ Nonempty (s ≅ t) :=
  ⟨Quotient.exact, fun h => @Quotient.sound _ (spanSetoid X Y) s t h⟩

/-- A pullback along a monomorphism of a morphism that already factors
through it has first projection an isomorphism. -/
def pullbackFactorIso {A B C : D} (f : A ⟶ C) (m : B ⟶ C) [Mono m]
    (a : A ⟶ B) (ha : a ≫ m = f) : pullback f m ≅ A where
  hom := pullback.fst _ _
  inv := pullback.lift (𝟙 A) a (by simpa using ha.symm)
  hom_inv_id := by
    apply pullback.hom_ext
    · simp
    · apply (cancel_mono m).mp
      simp only [Category.assoc, pullback.lift_snd_assoc]
      rw [ha, pullback.condition]
      simp
  inv_hom_id := by simp

namespace Raw

def restriction {X Y : Par D} (s : Raw X Y) : Raw X X :=
  ⟨s.apex, s.l, s.l, s.wl, by trivial⟩

def restrictionIso {X Y : Par D} {s t : Raw X Y} (i : s ≅ t) :
    s.restriction ≅ t.restriction := by
  let e : s.apex ≅ t.apex := CategoryTheory.Span.SpanBicat.apexIso i
  exact CategoryTheory.Span.mkIso e i.hom.hom_l i.hom.hom_l

def restrictCompSelfIso {X Y : Par D} (s : Raw X Y) : s.restriction ≫ s ≅ s := by
  have hm : pullback.fst s.l s.l = pullback.snd s.l s.l :=
    (cancel_mono s.l).mp pullback.condition
  refine CategoryTheory.Span.mkIso (pullbackFactorIso s.l s.l (𝟙 _) (by simp)) ?_ ?_
  · rfl
  · change pullback.fst s.l s.l ≫ s.r = pullback.snd s.l s.l ≫ s.r
    rw [hm]

def restrictionCommIso {X Y Z : Par D} (s : Raw X Y) (t : Raw X Z) :
    s.restriction ≫ t.restriction ≅ t.restriction ≫ s.restriction := by
  refine CategoryTheory.Span.mkIso (pullbackSymmetry s.l t.l) ?_ ?_
  · change (pullbackSymmetry s.l t.l).hom ≫ (pullback.fst t.l s.l ≫ t.l) =
      pullback.fst s.l t.l ≫ s.l
    rw [← Category.assoc, pullbackSymmetry_hom_comp_fst]
    exact pullback.condition.symm
  · change (pullbackSymmetry s.l t.l).hom ≫ (pullback.snd t.l s.l ≫ s.l) =
      pullback.snd s.l t.l ≫ t.l
    rw [← Category.assoc, pullbackSymmetry_hom_comp_snd]
    exact pullback.condition

def restrictionCompRestrictionIso {X Y Z : Par D} (s : Raw X Y) (t : Raw X Z) :
    restriction (s.restriction ≫ t : Raw X Z) ≅ s.restriction ≫ t.restriction := by
  refine CategoryTheory.Span.mkIso (Iso.refl _) ?_ ?_
  · exact Category.id_comp _
  · change 𝟙 (pullback s.l t.l) ≫ (pullback.snd s.l t.l ≫ t.l) =
      pullback.fst s.l t.l ≫ s.l
    rw [Category.id_comp]
    exact pullback.condition.symm

def restrictionCompIso {X Y Z : Par D} (s : Raw X Y) (t : Raw Y Z) :
    restriction (s ≫ t : Raw X Z) ≫ s ≅ s ≫ t.restriction := by
  have hh :
      pullback.fst (pullback.fst s.r t.l ≫ s.l) s.l ≫ pullback.fst s.r t.l =
        pullback.snd (pullback.fst s.r t.l ≫ s.l) s.l := by
    apply (cancel_mono s.l).mp
    simpa only [Category.assoc] using
      (pullback.condition (f := pullback.fst s.r t.l ≫ s.l) (g := s.l))
  refine CategoryTheory.Span.mkIso
    (pullbackFactorIso (pullback.fst s.r t.l ≫ s.l) s.l (pullback.fst s.r t.l) rfl)
    ?_ ?_
  · rfl
  · change pullback.fst (pullback.fst s.r t.l ≫ s.l) s.l ≫
        (pullback.snd s.r t.l ≫ t.l) =
      pullback.snd (pullback.fst s.r t.l ≫ s.l) s.l ≫ s.r
    rw [← pullback.condition, ← Category.assoc, hh]

end Raw

def parRst {X Y : Par D} : (X ⟶ Y) → (X ⟶ X) :=
  Quotient.map Raw.restriction (fun _ _ h => by
    obtain ⟨i⟩ := h
    exact ⟨Raw.restrictionIso i⟩)

@[simp] theorem parRst_ofSpan {X Y : Par D} (s : Raw X Y) :
    parRst (ofSpan s) = ofSpan s.restriction := rfl

instance parRestriction : RestrictionCategory (Par D) where
  rst := parRst
  rst_comp_self f := by
    induction f using Quotient.inductionOn with | _ s =>
      exact ofSpan_eq_of_iso (Raw.restrictCompSelfIso s)
  rst_comm f g := by
    induction f using Quotient.inductionOn with | _ s =>
      induction g using Quotient.inductionOn with | _ t =>
        exact ofSpan_eq_of_iso (Raw.restrictionCommIso s t)
  rst_comp_rst f g := by
    induction f using Quotient.inductionOn with | _ s =>
      induction g using Quotient.inductionOn with | _ t =>
        exact ofSpan_eq_of_iso (Raw.restrictionCompRestrictionIso s t)
  rst_comp f g := by
    induction f using Quotient.inductionOn with | _ s =>
      induction g using Quotient.inductionOn with | _ t =>
        exact ofSpan_eq_of_iso (Raw.restrictionCompIso s t)

@[simp] theorem rst_ofSpan {X Y : Par D} (s : Raw X Y) :
    rst (ofSpan s) = ofSpan s.restriction := rfl

namespace Raw

def total {X Y : Par D} (f : X.obj ⟶ Y.obj) : Raw X Y :=
  ⟨X.obj, 𝟙 _, f, inferInstance, by trivial⟩

def monoInverse {X Y : Par D} (m : X.obj ⟶ Y.obj) [Mono m] : Raw Y X :=
  ⟨X.obj, m, 𝟙 _, inferInstance, by trivial⟩

def totalCompIso {X Y Z : Par D} (f : X.obj ⟶ Y.obj) (g : Y.obj ⟶ Z.obj) :
    total f ≫ total g ≅ total (f ≫ g) := by
  refine CategoryTheory.Span.mkIso (pullbackFactorIso f (𝟙 _) f (by simp)) ?_ ?_
  · rfl
  · change pullback.fst f (𝟙 Y.obj) ≫ (f ≫ g) = pullback.snd f (𝟙 Y.obj) ≫ g
    rw [← Category.assoc, pullback.condition, Category.comp_id]

def totalMonoInverseIso {X Y : Par D} (m : X.obj ⟶ Y.obj) [Mono m] :
    total m ≫ monoInverse m ≅ 𝟙 (toSpanObject X) := by
  have hm : pullback.fst m m = pullback.snd m m :=
    (cancel_mono m).mp pullback.condition
  refine CategoryTheory.Span.mkIso (pullbackFactorIso m m (𝟙 _) (by simp)) ?_ ?_
  · rfl
  · change pullback.fst m m ≫ 𝟙 X.obj = pullback.snd m m ≫ 𝟙 X.obj
    rw [hm]

def monoInverseTotalIso {X Y : Par D} (m : X.obj ⟶ Y.obj) [Mono m] :
    monoInverse m ≫ total m ≅ (monoInverse m).restriction := by
  have hm : pullback.fst (𝟙 X.obj) (𝟙 X.obj) =
      pullback.snd (𝟙 X.obj) (𝟙 X.obj) := by
    simpa using (pullback.condition (f := 𝟙 X.obj) (g := 𝟙 X.obj))
  refine CategoryTheory.Span.mkIso
    (pullbackFactorIso (𝟙 X.obj) (𝟙 X.obj) (𝟙 _) (by simp)) ?_ ?_
  · rfl
  · change pullback.fst (𝟙 X.obj) (𝟙 X.obj) ≫ m =
      pullback.snd (𝟙 X.obj) (𝟙 X.obj) ≫ m
    rw [hm]

end Raw

/-- An ordinary morphism is represented by its span with identity domain. -/
def ofTotal {X Y : Par D} (f : X.obj ⟶ Y.obj) : X ⟶ Y := ofSpan (Raw.total f)

@[simp] theorem ofTotal_id (X : Par D) : ofTotal (𝟙 X.obj) = 𝟙 X := rfl

@[simp] theorem ofTotal_comp {X Y Z : Par D} (f : X.obj ⟶ Y.obj) (g : Y.obj ⟶ Z.obj) :
    ofTotal (f ≫ g) = ofTotal f ≫ ofTotal g :=
  (ofSpan_eq_of_iso (Raw.totalCompIso f g)).symm

theorem ofTotal_injective {X Y : Par D} :
    Function.Injective (ofTotal (X := X) (Y := Y)) := by
  intro f g h
  obtain ⟨i⟩ := (ofSpan_eq_iff (Raw.total f) (Raw.total g)).mp h
  have hi : i.hom.hom = 𝟙 X.obj := by
    simpa only [Raw.total, Category.comp_id] using i.hom.hom_l
  have hr := i.hom.hom_r
  simpa only [Raw.total, hi, Category.id_comp] using hr.symm

theorem ofTotal_total {X Y : Par D} (f : X.obj ⟶ Y.obj) : isTotal (ofTotal f) := rfl

def totalEmbedding : D ⥤ Par D where
  obj := Par.mk
  map := ofTotal
  map_id X := ofTotal_id (Par.mk X)
  map_comp := ofTotal_comp

instance totalEmbedding_faithful : (totalEmbedding (D := D)).Faithful where
  map_injective {X Y} f g h := @ofTotal_injective D _ _ (Par.mk X) (Par.mk Y) f g h

/-- The span `(m,1)` is the canonical partial inverse of a monomorphism. -/
def inverseMono {X Y : Par D} (m : X.obj ⟶ Y.obj) [Mono m] : Y ⟶ X :=
  ofSpan (Raw.monoInverse m)

@[simp] theorem total_inverseMono {X Y : Par D} (m : X.obj ⟶ Y.obj) [Mono m] :
    ofTotal m ≫ inverseMono m = 𝟙 X :=
  ofSpan_eq_of_iso (Raw.totalMonoInverseIso m)

@[simp] theorem inverseMono_total {X Y : Par D} (m : X.obj ⟶ Y.obj) [Mono m] :
    inverseMono m ≫ ofTotal m = rst (inverseMono m) :=
  ofSpan_eq_of_iso (Raw.monoInverseTotalIso m)

end CategoricalEssentialIncompleteness.V46.PartialMaps
