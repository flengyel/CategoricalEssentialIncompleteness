import CategoricalEssentialIncompleteness.V46NumericalRuleRebaseWords
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46

example {F G : NumericalTuples.Object} {N : ℕ} (R : RulePresentation F N) (e : F ≅ G)
    (x : NumericalTuples.Point (NumericalDerivation.codeObject R)) :
    NumericalTuples.code (NumericalDerivation.codeObject (NumericalRuleRebase.rules R e)).dimension
        ((NumericalRuleRebase.codeIso (F := F) (G := G) (N := N) R e).hom.toFun x).val =
      NumericalTuples.code (NumericalDerivation.codeObject R).dimension x.val :=
  NumericalRuleRebase.code_word_coded R e x

example {F G : NumericalTuples.Object} {N : ℕ} (R : RulePresentation F N) (e : F ≅ G)
    (x : NumericalTuples.Point (NumericalDerivation.codeObject (NumericalRuleRebase.rules R e))) :
    NumericalTuples.code (NumericalDerivation.codeObject R).dimension
        ((NumericalRuleRebase.codeIso (F := F) (G := G) (N := N) R e).inv.toFun x).val =
      NumericalTuples.code (NumericalDerivation.codeObject (NumericalRuleRebase.rules R e)).dimension x.val :=
  NumericalRuleRebase.inverse_code_word_coded R e x

example {F : NumericalTuples.Object} {N : ℕ} (R : RulePresentation F N) :
    (NumericalDerivation.codeObject R).dimension = 1 :=
  NumericalDerivation.codeObject_dimension R

example (x : NumericalTuples.Tuple 1) : NumericalTuples.code 1 x = x :=
  NumericalTuples.code_one x
