/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.EffectiveForkSpans
public import CategoricalEssentialIncompleteness.EffectiveForkTuring
public import CategoricalEssentialIncompleteness.FinitePowerCarriers

/-! # Constructed restriction-category structure on the computational fork -/

@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork

theorem locally_connected : LocallyConnected Object := inferInstance
theorem split : Splits Object := inferInstance
theorem weak_choice : WeakChoice Object := inferInstance
theorem inverse_image_joins : JoinInverse Object := inferInstance

theorem inducedRestriction_eq :
    (PCategory.inducedRestriction : RestrictionCategory Object) = forkRestriction := by
  have h : @RestrictionCategory.rst Object inferInstance PCategory.inducedRestriction =
      @RestrictionCategory.rst Object inferInstance forkRestriction := by
    funext X Y f
    exact induced_restriction f
  have extR : ∀ R S : RestrictionCategory Object,
      @RestrictionCategory.rst Object inferInstance R =
        @RestrictionCategory.rst Object inferInstance S → R = S := by
    intro R S
    cases R
    cases S
    intro he
    cases he
    rfl
  exact extR _ _ h

end CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork
