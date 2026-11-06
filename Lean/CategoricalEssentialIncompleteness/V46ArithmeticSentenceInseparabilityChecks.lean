import CategoricalEssentialIncompleteness.V46ArithmeticSentenceInseparability

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
namespace CategoricalEssentialIncompleteness.V46.ArithmeticSentenceInseparabilityChecks
open ArithmeticSentenceInseparability NamedArithmeticSignature
example (A : SyntacticPredicates.Carrier) (hPA : ArithmeticNamedAxiomComparison.ExtendsPA A)
    (hc : Entailment.Consistent (ArithmeticNamedProofConnectives.system A)) :
    Numerical.RecursivelyInseparable
      {word : ℕ | (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
        variableSymbols functionSymbols relationSymbols bound A).val.Evalb (M := ℕ) ![word]}
      {word : ℕ | (SyntacticGeneratedAxioms.literalRefutationCarrier 𝗣𝗔
        variableSymbols functionSymbols relationSymbols bound A).val.Evalb (M := ℕ) ![word]} :=
  recursively_inseparable A hPA hc
example (A B : SyntacticPredicates.Carrier) (hPA : ArithmeticNamedAxiomComparison.ExtendsPA A)
    (hAB : ∀ φ : NamedArithmeticSignature.Formula,
      A.val.Evalb (M := ℕ) ![formulaCode φ] → φ.freeVariables = [] →
        SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound B φ)
    (hc : Entailment.Consistent (ArithmeticNamedProofConnectives.system B)) :
    ∃ φ : NamedArithmeticSignature.Formula, φ.freeVariables = [] ∧
      ¬ SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound B φ ∧
      ¬ SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound B (.neg φ) :=
  extension_sentence_incomplete A B hPA hAB hc
example (A B : SyntacticPredicates.Carrier) (hPA : ArithmeticNamedAxiomComparison.ExtendsPA A)
    (hAB : ∀ φ : NamedArithmeticSignature.Formula,
      A.val.Evalb (M := ℕ) ![formulaCode φ] → φ.freeVariables = [] →
        SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound B φ)
    (hc : Entailment.Consistent (ArithmeticNamedProofConnectives.system B)) :
    Entailment.Incomplete (ArithmeticNamedProofConnectives.system B) :=
  extension_incomplete_system A B hPA hAB hc
example (A B : SyntacticPredicates.Carrier) (hPA : ArithmeticNamedAxiomComparison.ExtendsPA A)
    (hAB : ∀ word : ℕ, A.val.Evalb (M := ℕ) ![word] → B.val.Evalb (M := ℕ) ![word])
    (hc : Entailment.Consistent (ArithmeticNamedProofConnectives.system B)) :
    Entailment.Incomplete (ArithmeticNamedProofConnectives.system B) :=
  enumeration_extension_incomplete A B hPA hAB hc
end CategoricalEssentialIncompleteness.V46.ArithmeticSentenceInseparabilityChecks
