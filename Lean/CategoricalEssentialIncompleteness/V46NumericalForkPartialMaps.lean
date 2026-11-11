/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46RegularEquivalence
public import CategoricalEssentialIncompleteness.V46NumericalForkComparison
public import CategoricalEssentialIncompleteness.V46ForkRangeStability

/-! # Ordinary monic spans of numerical fork diagrams -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.NumericalForkPartialMaps

abbrev Diagram := WalkingSpan ⥤ NumericalTuples.Object

def totalEquivalence : Diagram ≌ EffectiveFork.Total := NumericalTuples.forkEquivalence.symm

instance diagramHasFiniteLimits : HasFiniteLimits Diagram where
  out _ := Adjunction.hasLimitsOfShape_of_equivalence totalEquivalence.functor

instance diagramHasFiniteCoproducts : HasFiniteCoproducts Diagram where
  out _ := Adjunction.hasColimitsOfShape_of_equivalence totalEquivalence.functor

instance diagramRegular : Regular Diagram :=
  RegularEquivalence.regular totalEquivalence.symm

instance diagramFinitaryExtensive : FinitaryExtensive Diagram :=
  finitaryExtensive_of_preserves_and_reflects_isomorphism totalEquivalence.functor

/-- The source is the literal quotient of ordinary monic spans in the
numerical diagram category, rather than a category of chosen codes. -/
def equivalence : PartialMaps.Par Diagram ≌ EffectiveFork.Object :=
  PartialMapEquivalence.equivalence totalEquivalence

theorem preserves_restrictions {X Y : PartialMaps.Par Diagram} (f : X ⟶ Y) :
    equivalence.functor.map (rst f) = rst (equivalence.functor.map f) :=
  PartialMapEquivalence.preserves_restrictions totalEquivalence f

theorem inverse_preserves_restrictions {X Y : EffectiveFork.Object} (f : X ⟶ Y) :
    equivalence.inverse.map (rst f) = rst (equivalence.inverse.map f) :=
  PartialMapEquivalence.inverse_preserves_restrictions totalEquivalence f

theorem preserves_ranges {X Y : PartialMaps.Par Diagram} (f : X ⟶ Y) :
    equivalence.functor.map (Ranges.range f).hom =
      (Ranges.range (equivalence.functor.map f)).hom :=
  PartialMapEquivalence.preserves_ranges totalEquivalence f

theorem span_range {X Y : PartialMaps.Par Diagram} (s : PartialMaps.Raw X Y) :
    Ranges.range (equivalence.functor.map (PartialMaps.ofSpan s)) =
      Ranges.range (totalEquivalence.functor.map s.r).hom :=
  ForkRangeStability.span_range (PartialMapEquivalence.mapSpan totalEquivalence s)

/-- Every total pullback of a value leg computes the inverse image of
the partial span's range, under the actual restriction/range comparison. -/
theorem span_pullback_range {X Y : PartialMaps.Par Diagram} (s : PartialMaps.Raw X Y)
    {P Z : Diagram} {p : P ⟶ s.apex} {q : P ⟶ Z} (g : Z ⟶ Y.obj)
    (h : IsPullback p q s.r g) :
    Ranges.range (totalEquivalence.functor.map q).hom =
      Idem.pull (totalEquivalence.functor.map g).hom
        (Ranges.range (equivalence.functor.map (PartialMaps.ofSpan s))) := by
  rw [span_range]
  exact EffectiveFork.pullback_image (totalEquivalence.functor.map_isPullback h)

end CategoricalEssentialIncompleteness.V46.NumericalForkPartialMaps
