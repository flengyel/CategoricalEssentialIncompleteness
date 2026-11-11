/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46KaroubiRestriction

/-! The restriction operation is checked on arbitrary idempotents. -/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Idempotents
open CategoricalEssentialIncompleteness.LocalConnectedness

example {C : Type u} [Category.{v} C] [RestrictionCategory C]
    (P Q : Karoubi C) (f : P ⟶ Q) : (rst f).f = P.p ≫ rst f.f :=
  V46.KaroubiRestriction.rst_f f

example {C : Type u} [Category.{v} C] [RestrictionCategory C]
    {X Y : C} (f : X ⟶ Y) :
    (toKaroubi C).map (rst f) = rst ((toKaroubi C).map f) :=
  V46.KaroubiRestriction.toKaroubi_preserves f

example {P Q : Karoubi EffectiveFork.Recursion.Rec} (f : P ⟶ Q) :
    EffectiveFork.Recursion.karoubiInclusion.map (rst f) =
      rst (EffectiveFork.Recursion.karoubiInclusion.map f) :=
  EffectiveFork.Recursion.karoubiInclusion_preserves_restrictions f

example {P Q : Karoubi EffectiveFork.Recursion.Rec} (f : P ⟶ Q) :
    EffectiveFork.Recursion.karoubiEquivalence.functor.map (rst f) =
      rst (EffectiveFork.Recursion.karoubiEquivalence.functor.map f) :=
  EffectiveFork.Recursion.karoubiEquivalence_preserves_restrictions f
