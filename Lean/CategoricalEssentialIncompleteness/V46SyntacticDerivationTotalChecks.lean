import CategoricalEssentialIncompleteness.V46SyntacticDerivationTotal

/-! The actual B_T/F endpoint has no chosen evaluator or initiality premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticDerivation
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] {F : TotalSplit T} {N : ℕ}
  (R : RulePresentation F N)
example : IsInitial (totalDerivationAlgebra T R) := totalDerivationInitial T R
example (i : Fin (N + 1)) : R.ruleObject (totalDerivationAlgebra T R).a i =
    pullback (R.premises i) (finitePowerMap (totalDerivationAlgebra T R).a.hom i.val) := rfl
example : (totalDerivationAlgebra T R).a.left =
    (predicateEquivalence T).functor.obj (totalDerivationCarrier T R) := totalDerivation_carrier T R
example : GraphMorphism T (totalDerivationCarrier T R) ((predicateEquivalence T).inverse.obj F) :=
  totalDerivationConclusionGraph T R
example : (totalDerivationAlgebra T R).a = Over.mk (totalDerivationConclusion T R) :=
  totalDerivation_conclusion T R
example : totalDerivationAlgebra T R ≅ totalChosenAlgebra T R := totalDerivationCodeIso T R
example : R.instances 0 ⟶ (totalDerivationAlgebra T R).a.left := totalNullaryDerivation T R
example : totalNullaryDerivation T R ≫ (totalDerivationAlgebra T R).a.hom = R.conclusion 0 :=
  totalNullaryDerivation_conclusion T R
example (B : Endofunctor.Algebra R.inference) (f : totalDerivationAlgebra T R ⟶ B) :
    f = totalDerivationFold T R B := totalDerivationFold_unique T R B f
example (B : Endofunctor.Algebra R.inference) :
    (totalDerivationFold T R B).f.left ≫ B.a.hom = totalDerivationConclusion T R :=
  totalDerivationFold_conclusion T R B
example (B : Endofunctor.Algebra R.inference) :
    (totalDerivationAlgebra T R).str ≫ (totalDerivationFold T R B).f =
      R.inference.map (totalDerivationFold T R B).f ≫ B.str := totalDerivationFold_constructor T R B
example :
    (totalDerivationAlgebra T R).str.left ≫ totalTreeInclusion T R =
      InputGeometry.forget R (totalDerivationAlgebra T R).a ≫
        (PolynomialComparison.ordinary R).map (totalTreeInclusion T R) ≫
          (totalOrdinaryTree T R).str := totalDerivationConstructor_tree T R
