import CategoricalEssentialIncompleteness.V46ArithmeticIndexedFibersAxiomsPredicate
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers
example (AxPA : Carrier) (e : ℕ) :
    IsPullback (fiberToFamilyPredicate AxPA e) (fiberSentencePredicate AxPA e)
      (ArithmeticIndexedAxioms.predicateInclusion AxPA)
      (rawNumeralPair ArithmeticIndexedAxioms.sentencePredicate e) := predicateAxiom_pullback AxPA e
example (B : PredicateCategory 𝗣𝗔) (e : ℕ) :
    rawNumeralPair B e ≫ SyntacticLists.fromRawProduct 𝗣𝗔 NamedArithmeticSignature.variableSymbols B =
      prod.lift (predicateTerminalFrom B ≫ numeralPredicate e) (𝟙 B) := rawNumeralPair_product B e
end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers
