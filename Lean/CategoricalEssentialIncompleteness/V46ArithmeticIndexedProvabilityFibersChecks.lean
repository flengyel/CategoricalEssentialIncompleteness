/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticIndexedProvabilityFibers


/-! # The numeral-fiber comparison for uniform provability -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedProvability.Checks
open NamedArithmeticSignature SyntacticPredicates
example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (AxPA : Carrier) (e : ℕ) (z : M) :
    (provability AxPA).val.Evalb ![(e : M),z] ↔
      (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔 variableSymbols functionSymbols
        relationSymbols bound (ArithmeticIndexedAxioms.fiberAxioms AxPA e)).val.Evalb ![z] :=
  provability_numeral M AxPA e z
example (AxPA : Carrier) (e : ℕ) : 𝗣𝗔 ⊢ numeralComparisonSentence AxPA e :=
  provability_numeral_PA AxPA e
example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (AxPA : Carrier) (e : ℕ) (z : M) :
    (programProvability AxPA).val.Evalb ![(e : M),z] ↔
      (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔 variableSymbols functionSymbols
        relationSymbols bound (ArithmeticIndexedAxioms.fiberAxioms AxPA e)).val.Evalb ![z] :=
  programProvability_numeral M AxPA e z
example (AxPA : Carrier) (e : ℕ) : 𝗣𝗔 ⊢ programNumeralComparisonSentence AxPA e :=
  programProvability_numeral_PA AxPA e
example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (AxPA : Carrier) (e : ℕ) (z : M) :
    (printedProvability AxPA).val.Evalb ![(e : M),z] ↔
      (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔 variableSymbols functionSymbols
        relationSymbols bound (ArithmeticIndexedAxioms.fiberAxioms AxPA e)).val.Evalb ![z] :=
  printedProvability_numeral M AxPA e z
example (AxPA : Carrier) (e : ℕ) : 𝗣𝗔 ⊢ printedNumeralComparisonSentence AxPA e :=
  printedProvability_numeral_PA AxPA e
example (AxPA : Carrier) (e : ℕ) :
    𝗣𝗔 ⊢ (let P := printedProvability AxPA
      let Q := SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔 variableSymbols functionSymbols
        relationSymbols bound (ArithmeticIndexedAxioms.fiberAxioms AxPA e)
      “∀ z, !P.val !!(e) z ↔ !Q.val z”) := printedProvability_numeral_PA AxPA e
end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedProvability.Checks
