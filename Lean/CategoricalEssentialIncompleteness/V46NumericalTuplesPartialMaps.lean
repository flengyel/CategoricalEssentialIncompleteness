/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalTuplesStructure
public import CategoricalEssentialIncompleteness.V46PartialMapEquivalence
public import CategoricalEssentialIncompleteness.V46PartialMapRanges

/-! # The full numerical tuple and ordinary monic-span realization -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.NumericalTuples

/-- The category uses ordinary monic spans of the tuple-function category, quotiented by
apex isomorphism. -/
abbrev PartialMapCategory := PartialMaps.Par Object

/-- Ordinary spans of tuple functions represent every partial recursive numerical carrier
map. -/
def numericalPartialMapEquivalence : PartialMapCategory ≌ EnumerableCarriers.Carrier :=
  PartialMapEquivalence.equivalence equivalence

/-- The numerical monic-span category presents the entire classical restriction splitting. -/
def partialMapEquivalence : PartialMapCategory ≌ SplitObject ClassicalPrograms.Rec :=
  numericalPartialMapEquivalence.trans EnumerableCarriers.classicalSplitEquivalence

theorem partialMap_preserves_restrictions {X Y : PartialMapCategory} (f : X ⟶ Y) :
    partialMapEquivalence.functor.map (rst f) =
      rst (partialMapEquivalence.functor.map f) := by
  change EnumerableCarriers.inclusion.map
      ((PartialMapEquivalence.functor equivalence).map (rst f)) =
    rst (EnumerableCarriers.inclusion.map ((PartialMapEquivalence.functor equivalence).map f))
  rw [PartialMapEquivalence.preserves_restrictions equivalence,
    EnumerableCarriers.inclusion_rst]

theorem inverse_preserves_restrictions {X Y : SplitObject ClassicalPrograms.Rec} (f : X ⟶ Y) :
    partialMapEquivalence.inverse.map (rst f) =
      rst (partialMapEquivalence.inverse.map f) :=
  LocalConnectedness.V46.equivalence_inverse_preserves partialMapEquivalence
    partialMap_preserves_restrictions f

theorem partialMap_preserves_ranges {X Y : PartialMapCategory} (f : X ⟶ Y) :
    partialMapEquivalence.functor.map (Ranges.range f).hom =
      (Ranges.range (partialMapEquivalence.functor.map f)).hom := by
  change EnumerableCarriers.inclusion.map
      ((PartialMapEquivalence.functor equivalence).map (Ranges.range f).hom) =
    (Ranges.range (EnumerableCarriers.inclusion.map
      ((PartialMapEquivalence.functor equivalence).map f))).hom
  rw [PartialMapEquivalence.preserves_ranges equivalence]
  rfl

end CategoricalEssentialIncompleteness.V46.NumericalTuples
