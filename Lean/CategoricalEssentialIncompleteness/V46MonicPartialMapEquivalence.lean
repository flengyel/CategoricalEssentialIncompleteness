/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MonicSpanValues
public import CategoricalEssentialIncompleteness.V46PartialMapEquivalence

/-! # Monic partial maps represent a split restriction category with partial inverses -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.MonicPartialMapEquivalence

open RestrictionSubobjects
open PartialMapEquivalence (mapSpan unmapSpan)

variable {D : Type u₁} [Category.{v₁} D] [HasPullbacks D]
variable {C : Type u₂} [Category.{v₂} C] [RestrictionCategory C] [Splits C]
variable [HasPullbacks (Tot C)]
variable (inverses : MonoInverses C) (E : D ≌ Tot C)

def mapHom {X Y : PartialMaps.Par D} : (X ⟶ Y) →
    ((E.functor.obj X.obj).obj ⟶ (E.functor.obj Y.obj).obj) :=
  Quotient.lift (fun s => MonicSpanValues.value inverses (mapSpan E s)) (by
    intro s t h
    obtain ⟨i⟩ := h
    exact MonicSpanValues.value_eq_of_isomorphic inverses
      (PartialMapEquivalence.mapSpan_isomorphic E i))

omit [Splits C] [HasPullbacks (Tot C)] in
theorem mapHom_ofSpan {X Y : PartialMaps.Par D} (s : PartialMaps.Raw X Y) :
    mapHom inverses E (PartialMaps.ofSpan s) =
      MonicSpanValues.value inverses (mapSpan E s) := rfl

theorem mapHom_comp {X Y Z : PartialMaps.Par D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    mapHom inverses E (f ≫ g) = mapHom inverses E f ≫ mapHom inverses E g := by
  induction f using Quotient.inductionOn with | _ s =>
    induction g using Quotient.inductionOn with | _ t =>
      change MonicSpanValues.value inverses (mapSpan E (s ≫ t)) = _
      exact (MonicSpanValues.value_eq_of_isomorphic inverses
        (PartialMapEquivalence.mapSpan_comp E s t)).trans
        (MonicSpanValues.value_pullbackComp inverses (mapSpan E s) (mapSpan E t))

omit [Splits C] [HasPullbacks (Tot C)] in
theorem mapHom_id (X : PartialMaps.Par D) : mapHom inverses E (𝟙 X) = 𝟙 _ := by
  change inverse inverses (E.functor.map (𝟙 X.obj)) ≫
    (E.functor.map (𝟙 X.obj)).hom = 𝟙 _
  simp only [E.functor.map_id]
  change inverse inverses (𝟙 (E.functor.obj X.obj)) ≫ (𝟙 _ : _ ⟶ _) = 𝟙 _
  have h := hom_inverse inverses (𝟙 (E.functor.obj X.obj))
  change (𝟙 _ : _ ⟶ _) ≫ inverse inverses (𝟙 (E.functor.obj X.obj)) = 𝟙 _ at h
  simpa only [Category.id_comp, Category.comp_id] using h

def functor : PartialMaps.Par D ⥤ C where
  obj X := (E.functor.obj X.obj).obj
  map := mapHom inverses E
  map_id := mapHom_id inverses E
  map_comp := mapHom_comp inverses E

instance functor_faithful : (functor inverses E).Faithful where
  map_injective {X Y} {f g} h := by
    induction f using Quotient.inductionOn with | _ s =>
      induction g using Quotient.inductionOn with | _ t =>
        apply Quotient.sound
        apply PartialMapEquivalence.reflect_span_iso E
        exact MonicSpanValues.isomorphic_of_value_eq inverses (mapSpan E s) (mapSpan E t) h

instance functor_full : (functor inverses E).Full where
  map_surjective f := by
    obtain ⟨s, hs⟩ := MonicSpanValues.exists_value inverses f
    exact ⟨PartialMaps.ofSpan (unmapSpan E s),
      (MonicSpanValues.value_eq_of_isomorphic inverses
        (PartialMapEquivalence.mapSpan_unmapSpan E s)).trans hs⟩

instance functor_essSurj : (functor inverses E).EssSurj where
  mem_essImage X := by
    let Y : Tot C := ⟨X⟩
    let i := E.counitIso.app Y
    let e : (E.functor.obj (E.inverse.obj Y)).obj ≅ X :=
      { hom := i.hom.hom
        inv := i.inv.hom
        hom_inv_id := congrArg (fun k => k.hom) i.hom_inv_id
        inv_hom_id := congrArg (fun k => k.hom) i.inv_hom_id }
    exact ⟨⟨E.inverse.obj Y⟩, ⟨e⟩⟩

instance functor_isEquivalence : (functor inverses E).IsEquivalence := {}

def equivalence : PartialMaps.Par D ≌ C := (functor inverses E).asEquivalence

theorem preserves_restrictions {X Y : PartialMaps.Par D} (f : X ⟶ Y) :
    (functor inverses E).map (rst f) = rst ((functor inverses E).map f) := by
  induction f using Quotient.inductionOn with | _ s =>
    change inverse inverses (E.functor.map s.l) ≫ (E.functor.map s.l).hom =
      rst (inverse inverses (E.functor.map s.l) ≫ (E.functor.map s.r).hom)
    rw [inverse_hom, rst_comp_of_isTotal _ (E.functor.map s.r).property]

theorem inverse_preserves_restrictions {X Y : C} (f : X ⟶ Y) :
    (equivalence inverses E).inverse.map (rst f) =
      rst ((equivalence inverses E).inverse.map f) :=
  LocalConnectedness.V46.equivalence_inverse_preserves (equivalence inverses E)
    (preserves_restrictions inverses E) f

/-- The comparison for the total category of C. -/
def selfEquivalence : PartialMaps.Par (Tot C) ≌ C :=
  equivalence inverses (CategoryTheory.Equivalence.refl (C := Tot C))

end CategoricalEssentialIncompleteness.V46.MonicPartialMapEquivalence
