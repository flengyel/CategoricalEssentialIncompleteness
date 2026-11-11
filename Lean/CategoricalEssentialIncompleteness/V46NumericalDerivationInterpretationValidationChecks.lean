/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationValidation


/-! # Statement checks in `V46NumericalDerivationInterpretationValidationChecks` -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
example {X W F : NumericalTuples.Object}
    (m : W ⟶ X) (h : W ⟶ F)
    (f g : X ⟶ OptionSyntax.obj F)
    (hf : IsPullback m h f (coprod.inr : F ⟶ OptionSyntax.obj F))
    (hg : IsPullback m h g (coprod.inr : F ⟶ OptionSyntax.obj F)) : f = g :=
  validator_unique m h f g hf hg
end CategoricalEssentialIncompleteness.V46.NumericalDerivationInterpretation
