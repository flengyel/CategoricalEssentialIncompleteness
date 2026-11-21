/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PartialMaps
public import CategoricalEssentialIncompleteness.V46PartialMapRanges
public import CategoricalEssentialIncompleteness.RestrictionSpanPullbacks
public import CategoricalEssentialIncompleteness.V46KaroubiRestriction
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Functor.EpiMono

/-! # Ordinary monic spans and a split restriction category's total category -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.PartialMapEquivalence

variable {D : Type u₁} [Category.{v₁} D] [HasPullbacks D]
variable {R : Type u₂} [Category.{v₂} R] [RestrictionCategory R]
variable [Splits R] [Ranges R] [WeakChoice R] [HasPullbacks (PartialSpans.Total R)]
variable (E : D ≌ PartialSpans.Total R)

def mapSpan {X Y : PartialMaps.Par D} (s : PartialMaps.Raw X Y) :
    PartialSpans.Span (E.functor.obj X.obj).obj (E.functor.obj Y.obj).obj where
  apex := E.functor.obj s.apex
  mono := E.functor.map s.l
  map := E.functor.map s.r
  monic := by infer_instance

omit [Splits R] [Ranges R] [WeakChoice R] [HasPullbacks (PartialSpans.Total R)] in
theorem mapSpan_isomorphic {X Y : PartialMaps.Par D} {s t : PartialMaps.Raw X Y}
    (i : s ≅ t) : (mapSpan E s).Isomorphic (mapSpan E t) := by
  let e := CategoryTheory.Span.SpanBicat.apexIso i
  refine ⟨E.functor.mapIso e, ?_, ?_⟩
  · change E.functor.map e.hom ≫ E.functor.map t.l = E.functor.map s.l
    rw [← E.functor.map_comp]
    exact congrArg E.functor.map i.hom.hom_l
  · change E.functor.map e.hom ≫ E.functor.map t.r = E.functor.map s.r
    rw [← E.functor.map_comp]
    exact congrArg E.functor.map i.hom.hom_r

omit [Splits R] [Ranges R] [WeakChoice R] [HasPullbacks (PartialSpans.Total R)] in
theorem reflect_span_iso {X Y : PartialMaps.Par D} {s t : PartialMaps.Raw X Y}
    (h : (mapSpan E s).Isomorphic (mapSpan E t)) : Nonempty (s ≅ t) := by
  obtain ⟨e, hl, hr⟩ := h
  let i := E.functor.preimageIso e
  have hi : E.functor.map i.hom = e.hom := E.functor.map_preimage _
  refine ⟨CategoryTheory.Span.mkIso i ?_ ?_⟩
  · apply E.functor.map_injective
    rw [E.functor.map_comp, hi]
    exact hl
  · apply E.functor.map_injective
    rw [E.functor.map_comp, hi]
    exact hr

def mapHom {X Y : PartialMaps.Par D} : (X ⟶ Y) →
    ((E.functor.obj X.obj).obj ⟶ (E.functor.obj Y.obj).obj) :=
  Quotient.lift (fun s => (mapSpan E s).value) (by
    intro s t h
    obtain ⟨i⟩ := h
    exact PartialSpans.Span.value_eq_of_isomorphic (mapSpan_isomorphic E i))

omit [HasPullbacks (PartialSpans.Total R)] in
@[simp] theorem mapHom_ofSpan {X Y : PartialMaps.Par D} (s : PartialMaps.Raw X Y) :
    mapHom E (PartialMaps.ofSpan s) = (mapSpan E s).value := rfl

omit [Splits R] [Ranges R] [WeakChoice R] in
theorem mapSpan_comp {X Y Z : PartialMaps.Par D} (s : PartialMaps.Raw X Y)
    (t : PartialMaps.Raw Y Z) :
    (mapSpan E (s ≫ t)).Isomorphic ((mapSpan E s).pullbackComp (mapSpan E t)) := by
  refine ⟨PreservesPullback.iso E.functor s.r t.l, ?_, ?_⟩
  · change (PreservesPullback.iso E.functor s.r t.l).hom ≫
      (pullback.fst (E.functor.map s.r) (E.functor.map t.l) ≫ E.functor.map s.l) =
        E.functor.map (pullback.fst s.r t.l ≫ s.l)
    rw [← Category.assoc, PreservesPullback.iso_hom_fst, E.functor.map_comp]
  · change (PreservesPullback.iso E.functor s.r t.l).hom ≫
      (pullback.snd (E.functor.map s.r) (E.functor.map t.l) ≫ E.functor.map t.r) =
        E.functor.map (pullback.snd s.r t.l ≫ t.r)
    rw [← Category.assoc, PreservesPullback.iso_hom_snd, E.functor.map_comp]

theorem mapHom_comp {X Y Z : PartialMaps.Par D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    mapHom E (f ≫ g) = mapHom E f ≫ mapHom E g := by
  induction f using Quotient.inductionOn with | _ s =>
    induction g using Quotient.inductionOn with | _ t =>
      change (mapSpan E (s ≫ t)).value = (mapSpan E s).value ≫ (mapSpan E t).value
      exact (PartialSpans.Span.value_eq_of_isomorphic (mapSpan_comp E s t)).trans
        ((mapSpan E s).value_pullbackComp (mapSpan E t))

omit [HasPullbacks (PartialSpans.Total R)] in
theorem mapHom_id (X : PartialMaps.Par D) : mapHom E (𝟙 X) = 𝟙 _ := by
  change PartialSpans.inverse (E.functor.map (𝟙 X.obj)) ≫
    (E.functor.map (𝟙 X.obj)).hom = 𝟙 _
  simp only [E.functor.map_id]
  change PartialSpans.inverse (𝟙 (E.functor.obj X.obj)) ≫
    (𝟙 _ : (E.functor.obj X.obj).obj ⟶ _) = 𝟙 _
  have h := PartialSpans.hom_inverse (𝟙 (E.functor.obj X.obj))
  change (𝟙 _ : (E.functor.obj X.obj).obj ⟶ _) ≫
    PartialSpans.inverse (𝟙 (E.functor.obj X.obj)) = 𝟙 _ at h
  simpa only [Category.id_comp, Category.comp_id] using h

def functor : PartialMaps.Par D ⥤ R where
  obj X := (E.functor.obj X.obj).obj
  map := mapHom E
  map_id := mapHom_id E
  map_comp := mapHom_comp E

instance functor_faithful : (functor E).Faithful where
  map_injective {X Y} {f g} h := by
    induction f using Quotient.inductionOn with | _ s =>
      induction g using Quotient.inductionOn with | _ t =>
        apply Quotient.sound
        apply reflect_span_iso E
        exact (mapSpan E s).isomorphic_of_value_eq (mapSpan E t) h

/-- Fullness of the base equivalence pulls every monic span back to an ordinary mono-left
span in D. -/
def unmapSpan {X Y : PartialMaps.Par D}
    (s : PartialSpans.Span (E.functor.obj X.obj).obj (E.functor.obj Y.obj).obj) :
    PartialMaps.Raw X Y := by
  let m := E.functor.preimage ((E.counitIso.app s.apex).hom ≫ s.mono)
  let f := E.functor.preimage ((E.counitIso.app s.apex).hom ≫ s.map)
  have hm : Mono m := by
    apply E.functor.mono_of_mono_map
    rw [show E.functor.map m = (E.counitIso.app s.apex).hom ≫ s.mono from
      E.functor.map_preimage _]
    infer_instance
  exact ⟨E.inverse.obj s.apex, m, f, hm, by trivial⟩

omit [Splits R] [Ranges R] [WeakChoice R] [HasPullbacks (PartialSpans.Total R)] in
theorem mapSpan_unmapSpan {X Y : PartialMaps.Par D}
    (s : PartialSpans.Span (E.functor.obj X.obj).obj (E.functor.obj Y.obj).obj) :
    (mapSpan E (unmapSpan E s)).Isomorphic s := by
  refine ⟨E.counitIso.app s.apex, ?_, ?_⟩
  · exact (E.functor.map_preimage _).symm
  · exact (E.functor.map_preimage _).symm

instance functor_full : (functor E).Full where
  map_surjective f := by
    obtain ⟨s, hs⟩ := PartialSpans.Span.exists_value f
    exact ⟨PartialMaps.ofSpan (unmapSpan E s),
      (PartialSpans.Span.value_eq_of_isomorphic (mapSpan_unmapSpan E s)).trans hs⟩

instance functor_essSurj : (functor E).EssSurj where
  mem_essImage X := by
    let Y : PartialSpans.Total R := ⟨X⟩
    let i := E.counitIso.app Y
    let e : (E.functor.obj (E.inverse.obj Y)).obj ≅ X :=
      { hom := i.hom.hom
        inv := i.inv.hom
        hom_inv_id := congrArg (fun k => k.hom) i.hom_inv_id
        inv_hom_id := congrArg (fun k => k.hom) i.inv_hom_id }
    exact ⟨⟨E.inverse.obj Y⟩, ⟨e⟩⟩

instance functor_isEquivalence : (functor E).IsEquivalence := {}

/-- The comparison is an equivalence of the monic-span quotient with R, and uses the
supplied equivalence only on its total category. -/
def equivalence : PartialMaps.Par D ≌ R := (functor E).asEquivalence

theorem preserves_restrictions {X Y : PartialMaps.Par D} (f : X ⟶ Y) :
    (functor E).map (rst f) = rst ((functor E).map f) := by
  induction f using Quotient.inductionOn with | _ s =>
    change PartialSpans.inverse (E.functor.map s.l) ≫ (E.functor.map s.l).hom =
      rst (PartialSpans.inverse (E.functor.map s.l) ≫ (E.functor.map s.r).hom)
    rw [PartialSpans.inverse_hom,
      rst_comp_of_isTotal _ (E.functor.map s.r).property]

theorem inverse_preserves_restrictions {X Y : R} (f : X ⟶ Y) :
    (equivalence E).inverse.map (rst f) = rst ((equivalence E).inverse.map f) :=
  LocalConnectedness.V46.equivalence_inverse_preserves (equivalence E)
    (preserves_restrictions E) f

/-- The represented range agrees with the source range whenever that
range is supplied, in particular for regular D. -/
theorem preserves_ranges [Ranges (PartialMaps.Par D)]
    {X Y : PartialMaps.Par D} (f : X ⟶ Y) :
    (functor E).map (Ranges.range f).hom = (Ranges.range ((functor E).map f)).hom := by
  let F := functor E
  let a := Ranges.range (F.map f)
  let b : Idem (F.obj Y) :=
    ⟨F.map (Ranges.range f).hom, by
      rw [← preserves_restrictions E, (Ranges.range f).restriction]⟩
  have hb : a ≤ b := Ranges.least (F.map f) b (by
    change F.map f ≫ F.map (Ranges.range f).hom = F.map f
    rw [← F.map_comp, Ranges.receives])
  have he : rst (F.preimage a.hom) = F.preimage a.hom := by
    apply F.map_injective
    rw [preserves_restrictions E, F.map_preimage]
    exact a.restriction
  let e : Idem Y := ⟨F.preimage a.hom, he⟩
  have hmap : F.map e.hom = a.hom := F.map_preimage _
  have hle : Ranges.range f ≤ e := Ranges.least f e (by
    apply F.map_injective
    rw [F.map_comp, hmap]
    exact Ranges.receives (F.map f))
  have hba : b ≤ a := by
    apply Idem.le_def.mpr
    change F.map (Ranges.range f).hom ≫ a.hom = F.map (Ranges.range f).hom
    rw [← hmap, ← F.map_comp]
    exact congrArg F.map (Idem.le_def.mp hle)
  exact congrArg Idem.hom (le_antisymm hba hb)

end CategoricalEssentialIncompleteness.V46.PartialMapEquivalence
