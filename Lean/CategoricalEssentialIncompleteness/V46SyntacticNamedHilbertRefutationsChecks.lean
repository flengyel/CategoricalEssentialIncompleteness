/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticNamedHilbertRefutations


/-! # Named negation proofs in the refutation image -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.SyntacticNamedHilbert.RefutationChecks
open SyntacticSyntax NamedFiniteSyntax NamedPostfixEncoding
variable (σ π : ℕ → Carrier) (d : ℕ) (Γ : Carrier)
variable (φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d)
example (h : Derives σ π d Γ (.neg φ)) (hs : φ.freeVariables = []) :
    (SyntacticGeneratedAxioms.literalRefutationCarrier
      𝗣𝗔 variableCarrier σ π d Γ).val.Evalb ![formulaCode φ] :=
  native_sentence_refutation σ π d Γ h hs
example (h : Derives σ π d Γ (.neg φ)) (hs : φ.freeVariables = []) :
    𝗣𝗔 ⊢ ((SyntacticGeneratedAxioms.literalRefutationCarrier
      𝗣𝗔 variableCarrier σ π d Γ).val/[(↑(formulaCode φ) : ArithmeticSemiterm Empty 0)] :
        ArithmeticSentence) := native_refutation_numeral_PA σ π d Γ h hs
end CategoricalEssentialIncompleteness.V46.SyntacticNamedHilbert.RefutationChecks
