/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticNamedHilbertRealization


/-! # Finite named proofs in the constructed Γ derivation object -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.SyntacticNamedHilbert.RealizationChecks
open NamedFiniteSyntax NamedPostfixEncoding SyntacticSyntax
variable (σ π : ℕ → Carrier) (d : ℕ) (Γ : Carrier)
variable (φ : NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d)

example (h : Derives σ π d Γ φ) :
    ∃ p : Obj 𝗣𝗔 ℕ (SyntacticGeneratedAxioms.proofs 𝗣𝗔 variableCarrier σ π d Γ).a.left,
      ((F 𝗣𝗔 ℕ).map (SyntacticGeneratedAxioms.conclusion 𝗣𝗔 variableCarrier σ π d Γ) p).val =
        formulaCode φ := native_realizes σ π d Γ h

example (h : Derives σ π d Γ φ) (hs : φ.freeVariables = []) :
    (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔 variableCarrier σ π d Γ).val.Evalb
      ![formulaCode φ] := native_sentence_theorem σ π d Γ h hs

example (h : Derives σ π d Γ φ) (hs : φ.freeVariables = []) :
    𝗣𝗔 ⊢ ((SyntacticGeneratedAxioms.literalTheoremCarrier
      𝗣𝗔 variableCarrier σ π d Γ).val/[(↑(formulaCode φ) : ArithmeticSemiterm Empty 0)] :
        ArithmeticSentence) := native_sentence_numeral_PA σ π d Γ h hs

end CategoricalEssentialIncompleteness.V46.SyntacticNamedHilbert.RealizationChecks
