/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalArithmeticProofWords


/-! # Statement checks in `V46NumericalArithmeticProofWordsChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open FailureOfComposition.ProofSearch
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.ProofWords.Checks
example (Γ : Carrier) : IsIso (comparison Γ) := comparison_isIso Γ
example (Γ : Carrier) : (iso Γ).hom ≫ ArithmeticLiteralModel.conclusion Γ =
    representedArrow 𝗣𝗔 (conclusion Γ) := iso_conclusion Γ
example (Γ : Carrier) : (iso Γ).hom ≫ pullback.fst
    (formulaConclusion Γ) arithmeticSyntax.sentenceInclusion = representedArrow 𝗣𝗔 (inclusion Γ) :=
  comparison_tree Γ
example (Γ : Carrier) (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (p : M) :
    (carrier Γ).val.Evalb ![p] ↔ ∃ z : M,
      (chosenGraph 𝗣𝗔 (formulaConclusion Γ)).graph.val.Evalb ![p,z] ∧
        ArithmeticLiteralModel.sentencePredicate.val.Evalb ![z] := carrier_eval M Γ p
example (Γ : Carrier) (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] (z : M) :
    (imageCarrier (conclusion Γ).graph).val.Evalb ![z] ↔
      (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
        NamedArithmeticSignature.variableSymbols NamedArithmeticSignature.functionSymbols
        NamedArithmeticSignature.relationSymbols NamedArithmeticSignature.bound Γ).val.Evalb ![z] :=
  fixed_provability M Γ z
end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.ProofWords.Checks
