import CategoricalEssentialIncompleteness.V46NumericalDerivation
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivation
example : interpretation.ReflectsIsomorphisms := inferInstance
example : PreservesLimitsOfShape WalkingCospan interpretation := inferInstance
example : PreservesColimitsOfShape (Discrete WalkingPair) interpretation := inferInstance
variable {F : NumericalTuples.Object} {N : ℕ} (R : RulePresentation F N)
example : IsInitial (ordinaryTree R) := ordinaryTreeInitial R
example : IsInitial (derivationAlgebra R) := derivationInitial R
example : (derivationAlgebra R).a =
    Over.mk (pullback.snd (validatorFold R).f (coprod.inr : F ⟶ OptionSyntax.obj F)) := derivation_carrier R
example : IsPullback (treeInclusion R) (conclusion R) (validatorFold R).f
    (coprod.inr : F ⟶ OptionSyntax.obj F) := successful_pullback R
example : (derivationAlgebra R).str.left ≫ treeInclusion R =
    SyntacticDerivation.InputGeometry.forget R (derivationAlgebra R).a ≫
      (SyntacticDerivation.PolynomialComparison.ordinary R).map (treeInclusion R) ≫ (ordinaryTree R).str :=
  constructor_tree R
example (B : Endofunctor.Algebra R.inference) :
    (derivationFold R B).f.left ≫ B.a.hom = conclusion R := fold_conclusion R B
example (B : Endofunctor.Algebra R.inference) :
    (derivationAlgebra R).str ≫ (derivationFold R B).f = R.inference.map (derivationFold R B).f ≫ B.str := fold_constructor R B
example (B : Endofunctor.Algebra R.inference) (f : derivationAlgebra R ⟶ B) :
    f = derivationFold R B := fold_unique R B f
example (B : Endofunctor.Algebra R.inference)
    (f : (derivationAlgebra R).a.left ⟶ B.a.left)
    (hf : f ≫ B.a.hom = conclusion R)
    (hc : R.inference.map (Over.homMk f hf) ≫ B.str =
      (derivationAlgebra R).str ≫ Over.homMk f hf) :
    f = (derivationFold R B).f.left := fold_underlying_unique R B f hf hc
example (i : Fin (N + 1)) :
    constructor R i ≫ conclusion R = R.ruleConclusion (derivationAlgebra R).a i := constructor_conclusion R i
example : nullary R ≫ conclusion R = R.conclusion 0 := nullary_conclusion R
end CategoricalEssentialIncompleteness.V46.NumericalDerivation
