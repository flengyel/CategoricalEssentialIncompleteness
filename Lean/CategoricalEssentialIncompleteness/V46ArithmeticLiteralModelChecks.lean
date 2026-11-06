import CategoricalEssentialIncompleteness.V46ArithmeticLiteralModel
import CategoricalEssentialIncompleteness.V46ArithmeticSetModelLaws

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.ArithmeticLiteralModel.Checks

example {A B : Type} (f : A → B) :
    CategoryTheory.RestrictionCategory.isTotal (ArithmeticSetModelLaws.someMap f) :=
  ArithmeticSetModelLaws.someMap_total f

example (Γ : Carrier) (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (s : Obj 𝗣𝗔 M sentencePredicate) :
    (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
      NamedArithmeticSignature.variableSymbols NamedArithmeticSignature.functionSymbols
      NamedArithmeticSignature.relationSymbols NamedArithmeticSignature.bound Γ).val.Evalb ![s.val] ↔
      ∃ p : Obj 𝗣𝗔 M (SyntacticGeneratedTheory.sentenceProofObject 𝗣𝗔
        NamedArithmeticSignature.variableSymbols NamedArithmeticSignature.functionSymbols
        NamedArithmeticSignature.relationSymbols NamedArithmeticSignature.bound (axioms Γ)),
        (F 𝗣𝗔 M).map (conclusion Γ) p = s := theorem_iff_image M Γ s

example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (s : Obj 𝗣𝗔 M sentencePredicate) :
    ((F 𝗣𝗔 M).map negation s).val = NamedArithmeticProofSearch.negationWord M s.val :=
  negation_value M s

end CategoricalEssentialIncompleteness.V46.ArithmeticLiteralModel.Checks
