import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationValidation
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
