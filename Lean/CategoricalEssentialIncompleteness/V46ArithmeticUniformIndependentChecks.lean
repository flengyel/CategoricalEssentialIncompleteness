/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticUniformIndependent


/-! # Statement checks in `V46ArithmeticUniformIndependentChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.ArithmeticUniformIndependentChecks
open NamedArithmeticSignature
example :
    ∃ q : @Quiver.Hom (TotalSplit 𝗣𝗔) inferInstance
        (ArithmeticOmegaComparison.identityOmega 𝗣𝗔) NamedArithmeticLiteralTotal.literalSentence,
      ∀ e : ℕ,
        Entailment.Consistent (ArithmeticNamedProofConnectives.system
          (ArithmeticIndexedAxioms.fiberAxioms ArithmeticIndexedPAEnumeration.axiomCodes e)) →
        ∃ φ : Formula, φ.freeVariables = [] ∧
          formulaCode φ =
            ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ).map q
              (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 ℕ e)).val.val ∧
          ¬ SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound
            (ArithmeticIndexedAxioms.fiberAxioms ArithmeticIndexedPAEnumeration.axiomCodes e) φ ∧
          ¬ SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound
            (ArithmeticIndexedAxioms.fiberAxioms ArithmeticIndexedPAEnumeration.axiomCodes e) (.neg φ) :=
  ArithmeticUniformIndependent.uniform_independent_sentences
example :
    ∃ q : @Quiver.Hom (TotalSplit 𝗣𝗔) inferInstance
        (ArithmeticOmegaComparison.identityOmega 𝗣𝗔) NamedArithmeticLiteralTotal.literalSentence,
      ∀ e : ℕ,
        Entailment.Consistent (ArithmeticNamedProofConnectives.system
          (ArithmeticIndexedAxioms.fiberAxioms ArithmeticIndexedPAEnumeration.axiomCodes e)) →
        let word := ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ).map q
          (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 ℕ e)).val.val
        ¬ (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
            variableSymbols functionSymbols relationSymbols bound
            (ArithmeticIndexedAxioms.fiberAxioms ArithmeticIndexedPAEnumeration.axiomCodes e)).val.Evalb ![word] ∧
          ¬ (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
            variableSymbols functionSymbols relationSymbols bound
            (ArithmeticIndexedAxioms.fiberAxioms ArithmeticIndexedPAEnumeration.axiomCodes e)).val.Evalb
              ![NamedArithmeticProofSearch.negationWord ℕ word] :=
  ArithmeticUniformIndependent.uniform_independent_sentence_codes
end CategoricalEssentialIncompleteness.V46.ArithmeticUniformIndependentChecks
