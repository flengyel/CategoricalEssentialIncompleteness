/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.EnumerableLimits
public import CategoricalEssentialIncompleteness.EnumerableFiniteCoproducts
public import CategoricalEssentialIncompleteness.EffectiveForkTotal
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! # Finite limits in the total fork category -/

@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork

instance totalHasFiniteLimits : HasFiniteLimits Total where
  out J := Adjunction.hasLimitsOfShape_of_equivalence totalEquivalence.functor

instance totalHasFiniteCoproducts : HasFiniteCoproducts Total where
  out J := Adjunction.hasColimitsOfShape_of_equivalence totalEquivalence.functor

end CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork
