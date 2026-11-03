/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46PartialMaps
import Mathlib.CategoryTheory.Widesubcategory

/-! # The total category of monic partial maps -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.PartialMaps

variable {D : Type u} [Category.{v} D] [HasPullbacks D]

namespace Raw

/-- A span is total precisely when its domain inclusion is invertible. -/
theorem left_isIso_of_total {X Y : Par D} (s : Raw X Y) (hs : isTotal (ofSpan s)) :
    IsIso s.l := by
  change ofSpan s.restriction = ofSpan (𝟙 (toSpanObject X)) at hs
  obtain ⟨i⟩ := (ofSpan_eq_iff s.restriction (𝟙 (toSpanObject X))).mp hs
  let e : s.apex ≅ X.obj := CategoryTheory.Span.SpanBicat.apexIso i
  have he : e.hom = s.l := by
    have h := i.hom.hom_l
    change i.hom.hom ≫ 𝟙 X.obj = s.l at h
    change i.hom.hom = s.l
    exact (Category.comp_id i.hom.hom).symm.trans h
  rw [← he]
  infer_instance

def totalIso {X Y : Par D} (s : Raw X Y) [IsIso s.l] :
    s ≅ total (inv s.l ≫ s.r) := by
  refine CategoryTheory.Span.mkIso (asIso s.l) ?_ ?_
  · exact Category.comp_id _
  · change s.l ≫ (inv s.l ≫ s.r) = s.r
    rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]

end Raw

/-- The ordinary morphism represented by a total partial map. -/
def totalValue {X Y : Par D} (f : X ⟶ Y) (hf : isTotal f) : X.obj ⟶ Y.obj := by
  let s := Quotient.out f
  have hs : isTotal (ofSpan s) := by simpa only [s, ofSpan, Quotient.out_eq] using hf
  letI := Raw.left_isIso_of_total s hs
  exact inv s.l ≫ s.r

@[simp] theorem ofTotal_totalValue {X Y : Par D} (f : X ⟶ Y) (hf : isTotal f) :
    ofTotal (totalValue f hf) = f := by
  let s := Quotient.out f
  have hs : isTotal (ofSpan s) := by simpa only [s, ofSpan, Quotient.out_eq] using hf
  let := Raw.left_isIso_of_total s hs
  change ofSpan (Raw.total (inv s.l ≫ s.r)) = f
  exact (ofSpan_eq_of_iso (Raw.totalIso s)).symm.trans (Quotient.out_eq f)

@[simp] theorem totalValue_ofTotal {X Y : Par D} (f : X.obj ⟶ Y.obj) :
    totalValue (ofTotal f) (ofTotal_total f) = f := by
  apply ofTotal_injective
  exact ofTotal_totalValue _ _

/-- An ordinary total morphism with a partial retraction is monic. -/
theorem totalValue_mono_of_retraction {T S : Par D} (m : T ⟶ S) (hm : isTotal m)
    (r : S ⟶ T) (hmr : m ≫ r = 𝟙 T) : Mono (totalValue m hm) := by
  constructor
  intro Z u v h
  let ZP : Par D := ⟨Z⟩
  apply @ofTotal_injective D _ _ ZP T u v
  have H := congrArg (fun f : Z ⟶ S.obj => ofTotal (X := ZP) (Y := S) f) h
  simp only [ofTotal_comp, ofTotal_totalValue] at H
  have H' := congrArg (fun f => f ≫ r) H
  simpa only [Category.assoc, hmr, Category.comp_id] using H'

abbrev Tot (D : Type u) [Category.{v} D] [HasPullbacks D] :=
  WideSubcategory (isTotal (C := Par D))

def toTotal : D ⥤ Tot D where
  obj X := ⟨Par.mk X⟩
  map f := ⟨ofTotal f, ofTotal_total f⟩
  map_id X := WideSubcategory.hom_ext _ (ofTotal_id (Par.mk X))
  map_comp f g := WideSubcategory.hom_ext _ (ofTotal_comp f g)

instance toTotal_faithful : (toTotal (D := D)).Faithful where
  map_injective {X Y} f g h := by
    apply @ofTotal_injective D _ _ (Par.mk X) (Par.mk Y) f g
    exact congrArg (fun q : (toTotal (D := D)).obj X ⟶ (toTotal (D := D)).obj Y => q.hom) h

instance toTotal_full : (toTotal (D := D)).Full where
  map_surjective f := ⟨totalValue f.hom f.property,
    WideSubcategory.hom_ext _ (ofTotal_totalValue f.hom f.property)⟩

instance toTotal_essSurj : (toTotal (D := D)).EssSurj where
  mem_essImage X := by
    refine ⟨X.obj.obj, ⟨eqToIso ?_⟩⟩
    cases X with | mk X =>
      cases X
      rfl

instance toTotal_isEquivalence : (toTotal (D := D)).IsEquivalence := {}

/-- The canonical total-arrow embedding is an equivalence onto all
total morphisms of the monic-span category. -/
def totalEquivalence : D ≌ Tot D := (toTotal (D := D)).asEquivalence

/-- The domain span itself supplies a splitting of every restriction
idempotent. No choice principle on partial monomorphisms is assumed. -/
instance parSplits : Splits (Par D) where
  splitting {X} a := by
    let s := Quotient.out a.hom
    let A : Par D := ⟨s.apex⟩
    let m : A ⟶ X := ofTotal s.l
    let r : X ⟶ A := inverseMono s.l
    refine ⟨A, m, r, ofTotal_total _, total_inverseMono _, ?_⟩
    have hs : ofSpan s = a.hom := Quotient.out_eq a.hom
    have ha : rst (ofSpan s) = a.hom := by rw [hs, a.restriction]
    rw [inverseMono_total]
    exact ha

end CategoricalEssentialIncompleteness.V46.PartialMaps
