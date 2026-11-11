/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46Karoubi

/-! # Explicit arbitrary-idempotent and Karoubi statements -/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Idempotents
open CategoricalEssentialIncompleteness.LocalConnectedness

noncomputable section

example {C : Type u} [Category.{v} C] [RestrictionCategory C] [Ranges C] [Splits C]
    {X : C} (f : X ⟶ X) (hf : f ≫ f = f) :
    ∃ (Y : C) (m : Y ⟶ X) (s : X ⟶ Y),
      isTotal m ∧ m ≫ s = 𝟙 Y ∧ s ≫ m = f :=
  V46.idempotent_splits_through_range f hf

example : IsIdempotentComplete EffectiveFork.Object :=
  EffectiveFork.idempotentComplete_v46

example : Karoubi EffectiveFork.Recursion.Rec ≌ EffectiveFork.Object :=
  EffectiveFork.Recursion.karoubiEquivalence

example : toKaroubi EffectiveFork.Recursion.Rec ⋙
    EffectiveFork.Recursion.karoubiEquivalence.functor ≅ EffectiveFork.Recursion.inclusion :=
  EffectiveFork.Recursion.karoubiEquivalence_source_iso
