import CategoricalEssentialIncompleteness.V46ArithmeticIndexedProvabilityModels
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedProvability.Checks
example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (AxPA : Carrier) (e z : M)
    (hs : NamedArithmeticLiteralTotal.literalPredicate.val.Evalb ![z]) :
    (provability AxPA).val.Evalb ![e,z] ↔
      ∃ p : (PredicateInterpretation.totalFunctor 𝗣𝗔 M).obj
          (ArithmeticIndexedFamily.sentenceProof AxPA),
        (PredicateInterpretation.totalFunctor 𝗣𝗔 M).map
          (ArithmeticIndexedFamily.sentenceConclusion AxPA) p = productPoint M e z hs :=
  provability_model M AxPA e z hs
end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedProvability.Checks
