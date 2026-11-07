import CategoricalEssentialIncompleteness.V46ArithmeticIndexedFibersPresentation
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers
example (AxPA : Carrier) (e : ℕ) :
    individualAlgebra AxPA e ≅ oldMappedAlgebra AxPA e := individual_oldGamma_comparison AxPA e
example (AxPA : Carrier) (e : ℕ) :
    (individual_oldGamma_formulaIso AxPA e).hom ≫
      (realization 𝗣𝗔).map (ArithmeticLiteralModel.formulaConclusion (gamma AxPA e)) =
        (individualAlgebra AxPA e).a.hom := individual_oldGamma_formula_conclusion AxPA e
example (AxPA : Carrier) (e : ℕ) :
    (individual_oldGamma_sentenceIso AxPA e).hom ≫
      (realization 𝗣𝗔).map (ArithmeticLiteralModel.conclusion (gamma AxPA e)) =
        individualSentenceConclusion AxPA e := individual_oldGamma_sentence_conclusion AxPA e
example (AxPA : Carrier) (e : ℕ) (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (s : (PredicateInterpretation.totalFunctor 𝗣𝗔 M).obj ArithmeticIndexedAxioms.sentence) :
    (ArithmeticLiteralModel.theoremPredicate (ArithmeticIndexedAxioms.fiberAxioms AxPA e)).val.Evalb
        ![((PredicateInterpretation.predicateComparison 𝗣𝗔 M).hom.app
          ArithmeticIndexedAxioms.sentencePredicate s).val] ↔
      ∃ p : (PredicateInterpretation.totalFunctor 𝗣𝗔 M).obj (individualSentenceProof AxPA e),
        (PredicateInterpretation.totalFunctor 𝗣𝗔 M).map (individualSentenceConclusion AxPA e) p = s :=
  individual_oldGamma_model AxPA e M s
end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers
