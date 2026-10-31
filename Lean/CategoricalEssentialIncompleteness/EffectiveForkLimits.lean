/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.EnumerableLimits
import CategoricalEssentialIncompleteness.EnumerableFiniteCoproducts
import CategoricalEssentialIncompleteness.EffectiveForkTotal
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! # Finite limits in the total fork category -/

noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork

instance totalHasFiniteLimits : HasFiniteLimits Total where
  out J := Adjunction.hasLimitsOfShape_of_equivalence totalEquivalence.functor

instance totalHasFiniteCoproducts : HasFiniteCoproducts Total where
  out J := Adjunction.hasColimitsOfShape_of_equivalence totalEquivalence.functor

end CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork
