/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ForkEssentialIncompleteness
public import Mathlib.CategoryTheory.Idempotents.Karoubi
public import Mathlib.CategoryTheory.Whiskering

/-! # Splitting arbitrary idempotents through their ranges -/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.Idempotents

namespace CategoricalEssentialIncompleteness.LocalConnectedness.V46

variable {C : Type u} [Category.{v} C] [RestrictionCategory C] [Ranges C] [Splits C]

/-- In a split restriction category with range agreement, an arbitrary
idempotent splits through the chosen splitting of its range. -/
theorem idempotent_splits_through_range {X : C} (f : X ⟶ X) (hf : f ≫ f = f) :
    ∃ (Y : C) (m : Y ⟶ X) (s : X ⟶ Y),
      isTotal m ∧ m ≫ s = 𝟙 Y ∧ s ≫ m = f := by
  let a := Ranges.range f
  obtain ⟨Y, m, r, hm, hmr, hrm⟩ := Splits.splitting a
  have haf : a.hom ≫ f = a.hom := by
    have h := Ranges.agreement f f (𝟙 X) (by simpa only [Category.comp_id] using hf)
    simpa only [Category.comp_id] using h
  have hma : m ≫ a.hom = m := by
    rw [← hrm, ← Category.assoc, hmr, Category.id_comp]
  have hmf : m ≫ f = m := by
    calc
      m ≫ f = (m ≫ a.hom) ≫ f := by rw [hma]
      _ = m ≫ a.hom := by rw [Category.assoc, haf]
      _ = m := hma
  refine ⟨Y, m, f ≫ r, hm, ?_, ?_⟩
  · rw [← Category.assoc, hmf, hmr]
  · rw [Category.assoc, hrm]
    exact Ranges.receives f

/-- The ambient split range category is idempotent complete in the
categorical sense used to form its Karoubi envelope. -/
theorem idempotentComplete : IsIdempotentComplete C := by
  constructor
  intro X f hf
  obtain ⟨Y, m, s, _, hms, hsm⟩ := idempotent_splits_through_range f hf
  exact ⟨Y, m, s, hms, hsm⟩

end CategoricalEssentialIncompleteness.LocalConnectedness.V46

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork

/-- Every idempotent natural partial fork map splits in the actual ambient
partial-map category, not only the restriction idempotents. -/
theorem idempotentComplete_v46 : IsIdempotentComplete Object :=
  V46.idempotentComplete

namespace Recursion

/-- The full inclusion extends to a functor on arbitrary idempotents. -/
def karoubiInclusion : Karoubi Rec ⥤ Karoubi Object where
  obj P := ⟨P.X.obj, P.p.hom, congrArg (fun f => f.hom) P.idem⟩
  map f := ⟨f.f.hom, congrArg (fun g => g.hom) f.comm⟩
  map_id _ := rfl
  map_comp _ _ := rfl

instance karoubiInclusion_faithful : karoubiInclusion.Faithful where
  map_injective h := Karoubi.hom_ext _ _
    (ObjectProperty.hom_ext _ (congrArg (fun f => f.f) h))

instance karoubiInclusion_full : karoubiInclusion.Full where
  map_surjective f :=
    ⟨⟨ObjectProperty.homMk f.f, ObjectProperty.hom_ext _ f.comm⟩, rfl⟩

/-- The universal fork contains a retract of each object, so the functor
on Karoubi envelopes is essentially surjective. -/
theorem karoubiInclusion_essSurj : karoubiInclusion.EssSurj := by
  constructor
  intro Q
  obtain ⟨m, r, _, hmr, _⟩ := dominance Q.X
  let p : V ⟶ V := r ≫ Q.p ≫ m
  have hp : p ≫ p = p := by
    dsimp [p]
    simp only [Category.assoc]
    rw [← Category.assoc m, hmr, Category.id_comp, ← Category.assoc Q.p, Q.idem]
  let P : Karoubi Rec :=
    ⟨U, ObjectProperty.homMk p, ObjectProperty.hom_ext _ hp⟩
  refine ⟨P, ⟨?_⟩⟩
  refine
    { hom := ⟨r ≫ Q.p, ?_⟩
      inv := ⟨Q.p ≫ m, ?_⟩
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · change p ≫ (r ≫ Q.p) ≫ Q.p = r ≫ Q.p
    dsimp [p]
    simp only [Category.assoc]
    rw [← Category.assoc m, hmr, Category.id_comp, ← Category.assoc Q.p, Q.idem, Q.idem]
  · change Q.p ≫ (Q.p ≫ m) ≫ p = Q.p ≫ m
    dsimp [p]
    simp only [Category.assoc]
    rw [← Category.assoc m, hmr, Category.id_comp]
    simp only [Q.idem_assoc]
  · apply Karoubi.hom_ext
    change (r ≫ Q.p) ≫ (Q.p ≫ m) = p
    dsimp [p]
    simp only [Category.assoc, Q.idem_assoc]
  · apply Karoubi.hom_ext
    change (Q.p ≫ m) ≫ (r ≫ Q.p) = Q.p
    simp only [Category.assoc]
    rw [← Category.assoc m, hmr, Category.id_comp, Q.idem]

instance karoubiInclusion_isEquivalence : karoubiInclusion.IsEquivalence := by
  let := karoubiInclusion_essSurj
  exact {}

/-- The Karoubi envelope of the generated recursion category is equivalent
to the actual ambient partial-map category. -/
def karoubiEquivalence : Karoubi Rec ≌ Object := by
  letI := idempotentComplete_v46
  exact karoubiInclusion.asEquivalence.trans (toKaroubiEquivalence Object).symm

/-- Before splitting the target idempotents, the extension agrees exactly
with the inclusion on every source object and morphism. -/
theorem karoubiInclusion_source :
    toKaroubi Rec ⋙ karoubiInclusion = inclusion ⋙ toKaroubi Object := rfl

/-- The equivalence extends the given full inclusion, with its natural
comparison on all source objects and morphisms. -/
def karoubiEquivalence_source_iso :
    toKaroubi Rec ⋙ karoubiEquivalence.functor ≅ inclusion := by
  letI := idempotentComplete_v46
  change toKaroubi Rec ⋙
      (karoubiInclusion ⋙ (toKaroubiEquivalence Object).inverse) ≅ inclusion
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (eqToIso karoubiInclusion_source) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft inclusion (toKaroubiEquivalence Object).unitIso.symm ≪≫
    Functor.rightUnitor inclusion

end Recursion

end CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork
