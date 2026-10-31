/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.EffectiveForkLimits
import CategoricalEssentialIncompleteness.EffectiveForkEvaluation
import CategoricalEssentialIncompleteness.EnumerablePullbackImages
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! # Component evaluation preserves total pullbacks and images are stable -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork

def totalEvaluation (j : Component) : Total ⥤ EnumerableCarriers.Total :=
  totalFunctor ⋙ (CategoryTheory.evaluation WalkingSpan EnumerableCarriers.Total).obj
    (match j with | .center => .zero | .left => .left | .right => .right)

instance totalEvaluation_preservesPullbacks (j : Component) :
    PreservesLimitsOfShape WalkingCospan (totalEvaluation j) := by
  letI : totalFunctor.IsEquivalence := totalEquivalence.isEquivalence_functor
  unfold totalEvaluation
  infer_instance

/-- Regular component images are stable under every pullback of total maps. -/
theorem pullback_image {P X Y Z : Total} {p : P ⟶ X} {q : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback p q f g) :
    Ranges.range q.hom=Idem.pull g.hom (Ranges.range f.hom) := by
  apply idem_ext
  · exact EnumerableCarriers.pullback_image ((totalEvaluation .center).map_isPullback h)
  · exact EnumerableCarriers.pullback_image ((totalEvaluation .left).map_isPullback h)
  · exact EnumerableCarriers.pullback_image ((totalEvaluation .right).map_isPullback h)

end CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork
