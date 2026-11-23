/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46TrivialDominicalCategory

/-! # The nonzero identity in the diagonal argument -/

@[expose] public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.PCategoryStruct CategoryTheory.CoprodStruct
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.TrivialDominicalCategory.Checks

theorem turing_with_separable_domains :
    DiPaolaHeller.IsTuringMorphism evaluator ∧ 𝟙 One.obj = (0 : One.obj ⟶ One.obj) ∧
      ¬ Inseparable (Idem.pull (diag One.obj ≫ evaluator) (summand0 One.obj One.obj))
        (Idem.pull (diag One.obj ≫ evaluator) (summand1 One.obj One.obj)) :=
  ⟨evaluator_turing, identity_eq_zero, diagonal_pair_separated⟩

end CategoricalEssentialIncompleteness.V46.TrivialDominicalCategory.Checks

open CategoricalEssentialIncompleteness.V46.TrivialDominicalCategory

#print axioms diagonal_pair_has_separator
#print axioms Checks.turing_with_separable_domains
