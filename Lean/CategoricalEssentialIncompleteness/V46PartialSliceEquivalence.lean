/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MonicPartialMapEquivalence
public import CategoricalEssentialIncompleteness.V46AmbientPartialSlice
public import CategoricalEssentialIncompleteness.V46PartialMapFunctor
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Monic partial spans in the total slice and ambient partial morphisms over T -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.PartialSliceEquivalence

open RestrictionSubobjects

variable {C : Type u} [Category.{v} C] [RestrictionCategory C] [Splits C]
variable [HasPullbacks (Tot C)]
variable (inverses : MonoInverses C) (T : Tot C)

local instance forget_preservesMonos : (Over.forget T).PreservesMonomorphisms where
  preserves f _ := Over.mono_left_of_mono f

def objectMap (X : PartialMaps.Par (Over T)) : AmbientPartialSlice.Family T.obj :=
  ⟨X.obj.left.obj, X.obj.hom.hom, X.obj.hom.property⟩

def underlyingSpan {X Y : PartialMaps.Par (Over T)} (s : PartialMaps.Raw X Y) :
    PartialSpans.Span X.obj.left.obj Y.obj.left.obj :=
  ⟨s.apex.left, s.l.left, s.r.left, by infer_instance⟩

def baseFunctor : PartialMaps.Par (Over T) ⥤ C :=
  PartialMaps.inducedFunctor (Over.forget T) ⋙
    MonicPartialMapEquivalence.functor inverses (CategoryTheory.Equivalence.refl (C := Tot C))

theorem baseMap_ofSpan {X Y : PartialMaps.Par (Over T)} (s : PartialMaps.Raw X Y) :
    (baseFunctor inverses T).map (PartialMaps.ofSpan s) =
      MonicSpanValues.value inverses (underlyingSpan T s) := rfl

theorem baseMap_over {X Y : PartialMaps.Par (Over T)} (f : X ⟶ Y) :
    (baseFunctor inverses T).map f ≫ Y.obj.hom.hom =
      rst ((baseFunctor inverses T).map f) ≫ X.obj.hom.hom := by
  induction f using Quotient.inductionOn with | _ s =>
    have hl : s.l.left.hom ≫ X.obj.hom.hom = s.apex.hom.hom :=
      congrArg (fun k => k.hom) (Over.w s.l)
    have hr : s.r.left.hom ≫ Y.obj.hom.hom = s.apex.hom.hom :=
      congrArg (fun k => k.hom) (Over.w s.r)
    change (inverse inverses s.l.left ≫ s.r.left.hom) ≫ Y.obj.hom.hom =
      rst (inverse inverses s.l.left ≫ s.r.left.hom) ≫ X.obj.hom.hom
    rw [Category.assoc, hr, ← hl, ← Category.assoc, inverse_hom,
      rst_comp_of_isTotal _ s.r.left.property]

def functor : PartialMaps.Par (Over T) ⥤ AmbientPartialSlice.Family T.obj where
  obj := objectMap T
  map f := ⟨(baseFunctor inverses T).map f, baseMap_over inverses T f⟩
  map_id X := AmbientPartialSlice.Hom.ext ((baseFunctor inverses T).map_id X)
  map_comp f g := AmbientPartialSlice.Hom.ext ((baseFunctor inverses T).map_comp f g)

instance functor_faithful : (functor inverses T).Faithful where
  map_injective {X Y} {f g} he := by
    induction f using Quotient.inductionOn with | _ s =>
      induction g using Quotient.inductionOn with | _ t =>
        have hv := congrArg AmbientPartialSlice.Hom.hom he
        change MonicSpanValues.value inverses (underlyingSpan T s) =
          MonicSpanValues.value inverses (underlyingSpan T t) at hv
        obtain ⟨i, hi, hr⟩ := MonicSpanValues.isomorphic_of_value_eq inverses
          (underlyingSpan T s) (underlyingSpan T t) hv
        change i.hom ≫ t.l.left = s.l.left at hi
        change i.hom ≫ t.r.left = s.r.left at hr
        have hw : i.hom ≫ t.apex.hom = s.apex.hom := by
          rw [← Over.w t.l, ← Category.assoc, hi, Over.w s.l]
        let e : s.apex ≅ t.apex := Over.isoMk i hw
        apply Quotient.sound
        refine ⟨CategoryTheory.Span.mkIso e ?_ ?_⟩
        · apply Over.OverMorphism.ext
          exact hi
        · apply Over.OverMorphism.ext
          exact hr

instance functor_full : (functor inverses T).Full where
  map_surjective {X Y} f := by
    obtain ⟨s, hs⟩ := MonicSpanValues.exists_value inverses f.hom
    have hmf : s.mono.hom ≫ f.hom = s.map.hom := by
      rw [← hs]
      change s.mono.hom ≫ (inverse inverses s.mono ≫ s.map.hom) = s.map.hom
      rw [← Category.assoc, hom_inverse, Category.id_comp]
    have hmr : s.mono.hom ≫ rst f.hom = s.mono.hom := by
      rw [← hs, MonicSpanValues.restrict_value, MonicSpanValues.hom_restrict_inverse]
    have hc : s.map.hom ≫ Y.obj.hom.hom = s.mono.hom ≫ X.obj.hom.hom := by
      have h := congrArg (fun k => s.mono.hom ≫ k) f.over
      change s.mono.hom ≫ (f.hom ≫ Y.obj.hom.hom) =
        s.mono.hom ≫ (rst f.hom ≫ X.obj.hom.hom) at h
      simpa only [← Category.assoc, hmf, hmr] using h
    let A : Over T := Over.mk (s.mono ≫ X.obj.hom)
    let l : A ⟶ X.obj := Over.homMk s.mono (by rfl)
    let r : A ⟶ Y.obj := Over.homMk s.map (by
      apply WideSubcategory.hom_ext
      exact hc)
    let w : PartialMaps.Raw X Y := ⟨A, l, r, by infer_instance, by trivial⟩
    refine ⟨PartialMaps.ofSpan w, AmbientPartialSlice.Hom.ext ?_⟩
    change MonicSpanValues.value inverses s = f.hom
    exact hs

instance functor_essSurj : (functor inverses T).EssSurj where
  mem_essImage X := by
    let p : (⟨X.base⟩ : Tot C) ⟶ T := ⟨X.proj, X.total⟩
    exact ⟨⟨Over.mk p⟩, ⟨Iso.refl X⟩⟩

instance functor_isEquivalence : (functor inverses T).IsEquivalence := {}

/-- The monic-span quotient in the total slice is the category of ambient partial
morphisms satisfying the partial over-T equation. -/
def equivalence : PartialMaps.Par (Over T) ≌ AmbientPartialSlice.Family T.obj :=
  (functor inverses T).asEquivalence

theorem preserves_restrictions {X Y : PartialMaps.Par (Over T)} (f : X ⟶ Y) :
    (functor inverses T).map (rst f) = rst ((functor inverses T).map f) := by
  apply AmbientPartialSlice.Hom.ext
  change (baseFunctor inverses T).map (rst f) = rst ((baseFunctor inverses T).map f)
  change (MonicPartialMapEquivalence.functor inverses
    (CategoryTheory.Equivalence.refl (C := Tot C))).map
      ((PartialMaps.inducedFunctor (Over.forget T)).map (rst f)) =
    rst ((MonicPartialMapEquivalence.functor inverses
      (CategoryTheory.Equivalence.refl (C := Tot C))).map
        ((PartialMaps.inducedFunctor (Over.forget T)).map f))
  rw [PartialMaps.inducedFunctor_restriction, MonicPartialMapEquivalence.preserves_restrictions]

theorem inverse_preserves_restrictions {X Y : AmbientPartialSlice.Family T.obj}
    (f : X ⟶ Y) :
    (equivalence inverses T).inverse.map (rst f) =
      rst ((equivalence inverses T).inverse.map f) :=
  LocalConnectedness.V46.equivalence_inverse_preserves (equivalence inverses T)
    (preserves_restrictions inverses T) f

theorem total_iff {X Y : PartialMaps.Par (Over T)} (f : X ⟶ Y) :
    isTotal ((functor inverses T).map f) ↔ isTotal f := by
  constructor
  · intro h
    apply (functor inverses T).map_injective
    rw [preserves_restrictions, h, (functor inverses T).map_id]
  · intro h
    change rst ((functor inverses T).map f) = 𝟙 _
    rw [← preserves_restrictions, h, (functor inverses T).map_id]

end CategoricalEssentialIncompleteness.V46.PartialSliceEquivalence
