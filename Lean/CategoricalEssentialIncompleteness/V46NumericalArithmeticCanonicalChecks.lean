import CategoricalEssentialIncompleteness.V46NumericalArithmeticCanonical
import CategoricalEssentialIncompleteness.V46ArithmeticLiteralModel
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory
open CategoricalEssentialIncompleteness.V46
open SyntacticPredicates

example (Γ : Carrier)
    (p : NumericalTuples.Point (NumericalArithmetic.numericalInterpretation.obj
      (ArithmeticLiteralModel.proofObject Γ))) :
    NumericalArithmetic.canonicalComparison.hom.app ArithmeticLiteralModel.sentencePredicate
        ((NumericalArithmetic.numericalInterpretation.map (ArithmeticLiteralModel.conclusion Γ)).toFun p) =
      (PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ).map
        ((realization 𝗣𝗔).map (ArithmeticLiteralModel.conclusion Γ))
          (NumericalArithmetic.canonicalComparison.hom.app (ArithmeticLiteralModel.proofObject Γ) p) :=
  NumericalArithmetic.canonicalComparison_natural (ArithmeticLiteralModel.conclusion Γ) p

example (Γ : Carrier)
    (p : NumericalTuples.Point (NumericalArithmetic.numericalInterpretation.obj
      (ArithmeticLiteralModel.proofObject Γ))) :
    (NumericalArithmetic.canonicalComparison.hom.app (ArithmeticLiteralModel.proofObject Γ) p).val.val = p.val :=
  NumericalArithmetic.canonicalComparison_value _ p
