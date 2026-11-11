/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PartialMapTotals
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Ranges in the generic monic-span partial-map category -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.PartialMaps

variable {D : Type u} [Category.{v} D] [Regular D]

namespace Raw

def totalLeftIso {X Y : Par D} (s : Raw X Y) :
    (total (X := Par.mk s.apex) (Y := X) s.l) ≫ s ≅
      total (X := Par.mk s.apex) (Y := Y) s.r := by
  have hm : pullback.fst s.l s.l = pullback.snd s.l s.l :=
    (cancel_mono s.l).mp pullback.condition
  refine CategoryTheory.Span.mkIso
    (pullbackFactorIso s.l s.l (𝟙 _) (by simp)) ?_ ?_
  · rfl
  · change pullback.fst s.l s.l ≫ s.r = pullback.snd s.l s.l ≫ s.r
    rw [hm]

def rangeSpan {X Y : Par D} (s : Raw X Y) : Raw Y Y :=
  ⟨image s.r, image.ι s.r, image.ι s.r, inferInstance, by trivial⟩

def rangeReceivesIso {X Y : Par D} (s : Raw X Y) : s ≫ rangeSpan s ≅ s := by
  refine CategoryTheory.Span.mkIso
    (pullbackFactorIso s.r (image.ι s.r) (factorThruImage s.r) (image.fac s.r)) ?_ ?_
  · rfl
  · exact pullback.condition

end Raw

theorem total_left_ofSpan {X Y : Par D} (s : Raw X Y) :
    ofTotal (X := Par.mk s.apex) (Y := X) s.l ≫ ofSpan s =
      ofTotal (X := Par.mk s.apex) (Y := Y) s.r :=
  ofSpan_eq_of_iso (Raw.totalLeftIso s)

/-- A regular epimorphism remains epic against partial maps. The proof
descends the domain isomorphism by regular-epi/mono lifting. -/
instance ofTotal_regularEpi_epi {X Y : Par D} (e : X.obj ⟶ Y.obj) [IsRegularEpi e] :
    Epi (ofTotal e) where
  left_cancellation {Z} g h H := by
    induction g using Quotient.inductionOn with | _ s =>
      induction h using Quotient.inductionOn with | _ t =>
        change ofSpan (Raw.total e ≫ s) = ofSpan (Raw.total e ≫ t) at H
        obtain ⟨i⟩ := (ofSpan_eq_iff _ _).mp H
        let j : pullback e s.l ≅ pullback e t.l :=
          CategoryTheory.Span.SpanBicat.apexIso i
        have hj : j.hom ≫ pullback.fst e t.l = pullback.fst e s.l := by
          have h := i.hom.hom_l
          change j.hom ≫ (pullback.fst e t.l ≫ 𝟙 X.obj) =
            pullback.fst e s.l ≫ 𝟙 X.obj at h
          simpa only [Category.comp_id] using h
        have hk : j.inv ≫ pullback.fst e s.l = pullback.fst e t.l := by
          have h := i.inv.hom_l
          change j.inv ≫ (pullback.fst e s.l ≫ 𝟙 X.obj) =
            pullback.fst e t.l ≫ 𝟙 X.obj at h
          simpa only [Category.comp_id] using h
        have sq : CommSq (j.hom ≫ pullback.snd e t.l) (pullback.snd e s.l)
            t.l s.l := by
          constructor
          rw [Category.assoc, ← pullback.condition, ← Category.assoc, hj, pullback.condition]
        have sq' : CommSq (j.inv ≫ pullback.snd e s.l) (pullback.snd e t.l)
            s.l t.l := by
          constructor
          rw [Category.assoc, ← pullback.condition, ← Category.assoc, hk, pullback.condition]
        let u := sq.lift
        let w := sq'.lift
        have hu : u ≫ t.l = s.l := sq.fac_right
        have hw : w ≫ s.l = t.l := sq'.fac_right
        have huw : u ≫ w = 𝟙 s.apex := by
          apply (cancel_mono s.l).mp
          rw [Category.assoc, hw, hu, Category.id_comp]
        have hwu : w ≫ u = 𝟙 t.apex := by
          apply (cancel_mono t.l).mp
          rw [Category.assoc, hu, hw, Category.id_comp]
        apply ofSpan_eq_of_iso
        refine CategoryTheory.Span.mkIso ⟨u, w, huw, hwu⟩ hu ?_
        apply (cancel_epi (pullback.snd e s.l)).mp
        rw [← Category.assoc, sq.fac_left, Category.assoc]
        have hr := i.hom.hom_r
        change j.hom ≫ (pullback.snd e t.l ≫ t.r) =
          pullback.snd e s.l ≫ s.r at hr
        exact hr

theorem rangeSpan_agreement {X Y Z : Par D} (s : Raw X Y) (g h : Y ⟶ Z)
    (H : ofSpan s ≫ g = ofSpan s ≫ h) :
    ofSpan (Raw.rangeSpan s) ≫ g = ofSpan (Raw.rangeSpan s) ≫ h := by
  let I : Par D := ⟨image s.r⟩
  let ep : Par.mk s.apex ⟶ I := ofTotal (factorThruImage s.r)
  let m : I ⟶ Y := ofTotal (image.ι s.r)
  let q : Y ⟶ I := inverseMono (image.ι s.r)
  have H' : ofTotal (X := Par.mk s.apex) (Y := Y) s.r ≫ g =
      ofTotal (X := Par.mk s.apex) (Y := Y) s.r ≫ h := by
    have hh := congrArg (fun k => ofTotal (X := Par.mk s.apex) (Y := X) s.l ≫ k) H
    simpa only [← Category.assoc, total_left_ofSpan] using hh
  have hem : ep ≫ m = ofTotal (X := Par.mk s.apex) (Y := Y) s.r := by
    dsimp [ep, m]
    rw [← ofTotal_comp, image.fac]
  have hcancel : ep ≫ (m ≫ g) = ep ≫ (m ≫ h) := by
    simpa only [← Category.assoc, hem] using H'
  have hmg : m ≫ g = m ≫ h := (cancel_epi ep).mp hcancel
  have hq := congrArg (fun k => q ≫ k) hmg
  have hqm : q ≫ m = rst q := inverseMono_total (X := I) (Y := Y) (image.ι s.r)
  change rst q ≫ g = rst q ≫ h
  simpa only [← Category.assoc, hqm] using hq

/-- The range is the partial identity on the regular image of the
right leg of a chosen span representative. -/
def parRange {X Y : Par D} (f : X ⟶ Y) : Idem Y :=
  ⟨ofSpan (Raw.rangeSpan (Quotient.out f)), rfl⟩

instance parRanges : Ranges (Par D) where
  range := parRange
  receives f := by
    let s := Quotient.out f
    have hs : ofSpan s = f := Quotient.out_eq f
    change f ≫ ofSpan (Raw.rangeSpan s) = f
    rw [← hs]
    exact ofSpan_eq_of_iso (Raw.rangeReceivesIso s)
  agreement f g h H := by
    let s := Quotient.out f
    have hs : ofSpan s = f := Quotient.out_eq f
    change ofSpan (Raw.rangeSpan s) ≫ g = ofSpan (Raw.rangeSpan s) ≫ h
    apply rangeSpan_agreement s g h
    rw [hs]
    exact H

/-- The image formula is independent of the representative selected in
the definition of `parRange`. -/
theorem range_ofSpan {X Y : Par D} (s : Raw X Y) :
    Ranges.range (ofSpan s) =
      (⟨ofSpan (Raw.rangeSpan s), rfl⟩ : Idem Y) := by
  apply le_antisymm
  · exact Ranges.least _ _ (ofSpan_eq_of_iso (Raw.rangeReceivesIso s))
  · change ofSpan (Raw.rangeSpan s) ≫ (Ranges.range (ofSpan s)).hom =
      ofSpan (Raw.rangeSpan s)
    have h := rangeSpan_agreement s (Ranges.range (ofSpan s)).hom (𝟙 Y)
      (by rw [Ranges.receives, Category.comp_id])
    simpa only [Category.comp_id] using h

end CategoricalEssentialIncompleteness.V46.PartialMaps
