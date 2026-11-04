import CategoricalEssentialIncompleteness.V46PartialMapEquivalence

/-! # All monic spans through a proved equivalence of total categories -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46

variable {D : Type u₁} [Category.{v₁} D] [HasPullbacks D]
variable {R : Type u₂} [Category.{v₂} R] [RestrictionCategory R]
variable [Splits R] [Ranges R] [WeakChoice R] [HasPullbacks (PartialSpans.Total R)]
variable (E : D ≌ PartialSpans.Total R)

example : PartialMaps.Par D ≌ R := PartialMapEquivalence.equivalence E

example {X Y : PartialMaps.Par D} (f : X ⟶ Y) :
    (PartialMapEquivalence.equivalence E).functor.map (rst f) =
      rst ((PartialMapEquivalence.equivalence E).functor.map f) :=
  PartialMapEquivalence.preserves_restrictions E f

example {X Y : R} (f : X ⟶ Y) :
    (PartialMapEquivalence.equivalence E).inverse.map (rst f) =
      rst ((PartialMapEquivalence.equivalence E).inverse.map f) :=
  PartialMapEquivalence.inverse_preserves_restrictions E f

example [Ranges (PartialMaps.Par D)] {X Y : PartialMaps.Par D} (f : X ⟶ Y) :
    (PartialMapEquivalence.equivalence E).functor.map (Ranges.range f).hom =
      (Ranges.range ((PartialMapEquivalence.equivalence E).functor.map f)).hom :=
  PartialMapEquivalence.preserves_ranges E f
