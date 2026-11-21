/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalTuplesPartialMaps

/-! Tuple total category and ordinary monic-span restriction equivalences. -/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.NumericalTuples

example : Object ≌ EnumerableCarriers.Total := equivalence
example : Object ≌ PartialSpans.Total (SplitObject ClassicalPrograms.Rec) :=
  classicalTotalEquivalence
example : PartialMaps.Par Object ≌ SplitObject ClassicalPrograms.Rec := partialMapEquivalence
example : CategoryTheory.Regular Object := inferInstance
example : CategoryTheory.FinitaryExtensive Object := inferInstance

example {X Y : PartialMapCategory} (f : X ⟶ Y) :
    partialMapEquivalence.functor.map (rst f) = rst (partialMapEquivalence.functor.map f) :=
  partialMap_preserves_restrictions f

example {X Y : SplitObject ClassicalPrograms.Rec} (f : X ⟶ Y) :
    partialMapEquivalence.inverse.map (rst f) = rst (partialMapEquivalence.inverse.map f) :=
  inverse_preserves_restrictions f

example {X Y : PartialMapCategory} (f : X ⟶ Y) :
    partialMapEquivalence.functor.map (Ranges.range f).hom =
      (Ranges.range (partialMapEquivalence.functor.map f)).hom := partialMap_preserves_ranges f
