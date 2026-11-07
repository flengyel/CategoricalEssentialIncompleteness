import CategoricalEssentialIncompleteness.V46ArithmeticIndexedProvabilityExponential

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedProvability.ExponentialChecks
open NamedArithmeticSignature

example : (realization 𝗣𝗔).obj
    (ExponentialProducts.carrier variableSymbols ArithmeticIndexedAxioms.sentencePredicate) ≅
      ArithmeticIndexedAxioms.parameter ⨯ ArithmeticIndexedAxioms.sentence := printedProductIso

example (AxPA : Carrier) :
    printedConclusion AxPA = rawConclusion AxPA ≫
      (ExponentialProducts.rawProductIso 𝗣𝗔 variableSymbols ArithmeticIndexedAxioms.sentencePredicate).hom :=
  printedConclusion_eq AxPA

example (AxPA : Carrier) :
    (realization 𝗣𝗔).map (printedConclusion AxPA) =
      (proofPresentationIso AxPA).hom ≫ ArithmeticIndexedFamily.sentenceConclusion AxPA ≫
        printedProductIso.inv := printedConclusion_realization AxPA

example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (AxPA : Carrier) (p w : M) :
    UniformTrace.graph.val.Evalb ![(printedConclusionIndex AxPA : M),p,w] ↔
      (printedRepresentation AxPA).graph.val.Evalb ![p,w] :=
  printedConclusionIndex_graph M AxPA p w

example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (AxPA : Carrier) (e z : M) :
    (∃ p : M, UniformTrace.graph.val.Evalb
      ![(printedConclusionIndex AxPA : M),p,ExponentialPairing.code e z]) ↔
        (provability AxPA).val.Evalb ![e,z] :=
  (printedProvability_code M AxPA e z).symm.trans (printedProvability_eval M AxPA e z)

example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (AxPA : Carrier) (p : M) :
    (∃ w : M, UniformTrace.graph.val.Evalb ![(printedConclusionIndex AxPA : M),p,w]) ↔
      (proofCarrier AxPA).val.Evalb ![p] := printedConclusionIndex_domain M AxPA p

example (AxPA : Carrier) : 𝗣𝗔 ⊢ printedConclusionIndexGraphSentence AxPA :=
  printedConclusionIndex_graph_PA AxPA
example (AxPA : Carrier) : 𝗣𝗔 ⊢ printedConclusionIndexDomainSentence AxPA :=
  printedConclusionIndex_domain_PA AxPA
example (AxPA : Carrier) : 𝗣𝗔 ⊢ printedProvabilityComparisonSentence AxPA :=
  printedProvability_comparison_PA AxPA

end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedProvability.ExponentialChecks
