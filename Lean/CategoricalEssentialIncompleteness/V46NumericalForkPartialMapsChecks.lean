/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalForkPartialMaps

/-! The source of the span comparison is the numerical diagram category. -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46
open NumericalForkPartialMaps

example : Regular (WalkingSpan ⥤ NumericalTuples.Object) := inferInstance
example : FinitaryExtensive (WalkingSpan ⥤ NumericalTuples.Object) := inferInstance
example : Splits (PartialMaps.Par (WalkingSpan ⥤ NumericalTuples.Object)) := inferInstance
example : Ranges (PartialMaps.Par (WalkingSpan ⥤ NumericalTuples.Object)) := inferInstance
example : PartialMaps.Par (WalkingSpan ⥤ NumericalTuples.Object) ≌ EffectiveFork.Object :=
  equivalence

example {X Y : PartialMaps.Par Diagram} (f : X ⟶ Y) :
    equivalence.functor.map (rst f) = rst (equivalence.functor.map f) :=
  preserves_restrictions f

example {X Y : EffectiveFork.Object} (f : X ⟶ Y) :
    equivalence.inverse.map (rst f) = rst (equivalence.inverse.map f) :=
  inverse_preserves_restrictions f

example {X Y : PartialMaps.Par Diagram} (f : X ⟶ Y) :
    equivalence.functor.map (Ranges.range f).hom =
      (Ranges.range (equivalence.functor.map f)).hom :=
  preserves_ranges f

example {X Y : PartialMaps.Par Diagram} (s : PartialMaps.Raw X Y)
    {P Z : Diagram} {p : P ⟶ s.apex} {q : P ⟶ Z} (g : Z ⟶ Y.obj)
    (h : IsPullback p q s.r g) :
    Ranges.range (totalEquivalence.functor.map q).hom =
      Idem.pull (totalEquivalence.functor.map g).hom
        (Ranges.range (equivalence.functor.map (PartialMaps.ofSpan s))) :=
  span_pullback_range s g h
