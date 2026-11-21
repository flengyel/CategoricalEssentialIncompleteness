/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticNamedHilbertRealization
public import CategoricalEssentialIncompleteness.V46SyntacticGeneratedRefutations

/-! # Named negation proofs in the refutation image -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.SyntacticNamedHilbert
open SyntacticSyntax NamedFiniteSyntax NamedPostfixEncoding ConcreteNamedComparison
variable (σ π : ℕ → Carrier) (d : ℕ) (Γ : Carrier)
local notation "S" => plainCategoricalSyntax 𝗣𝗔 variableCarrier σ π d
local notation "Fm" => NamedFiniteSyntax.Formula (Symbols σ) (Symbols π) d
local notation "G" => F 𝗣𝗔 ℕ

/-- Negation is read through the graph of the categorical constructor; its input and
output are literal formula words. -/
theorem negation_graph_word (φ : Fm) :
    (chosenGraph 𝗣𝗔 (S).negationConstructor).graph.val.Evalb
      ![formulaCode φ,formulaCode (.neg φ)] := by
  have he : ((G).map (S).negationConstructor (formulaPoint σ π d φ)).val =
      formulaCode (.neg φ) :=
    (congrArg Subtype.val (negation_point σ π d φ)).trans
      (formulaPoint_value σ π d (.neg φ))
  have hg := (chosenGraph_value_iff 𝗣𝗔 ℕ (S).negationConstructor
    (formulaPoint σ π d φ) (formulaCode (.neg φ))).mpr he
  simpa only [formulaPoint_value] using hg

/-- A Hilbert proof of the negation supplies the refutation predicate of the original
sentence, with an existential negative word. -/
theorem native_sentence_refutation {φ : Fm} (h : Derives σ π d Γ (.neg φ))
    (hs : φ.freeVariables = []) :
    (SyntacticGeneratedAxioms.literalRefutationCarrier
      𝗣𝗔 variableCarrier σ π d Γ).val.Evalb ![formulaCode φ] := by
  apply (SyntacticGeneratedAxioms.literalRefutationCarrier_eval
    𝗣𝗔 variableCarrier σ π d ℕ Γ (formulaCode φ)).mpr
  refine ⟨?_,formulaCode (.neg φ),negation_graph_word σ π d φ,?_⟩
  · apply (literalSentenceCarrier_eval 𝗣𝗔 variableCarrier σ π d ℕ _).mpr
    constructor
    · simpa only [formulaPoint_value,termPolynomial,formulaPolynomial] using (formulaPoint σ π d φ).property
    · exact (@sentence_formulaCode_iff σ π d φ).mpr hs
  · apply native_sentence_theorem σ π d Γ h
    exact hs

/-- Individual refutation membership also has its PA numeral proof;
this does not assert PA proves consistency of the enumerated theory. -/
theorem native_refutation_numeral_PA {φ : Fm} (h : Derives σ π d Γ (.neg φ))
    (hs : φ.freeVariables = []) :
    𝗣𝗔 ⊢ ((SyntacticGeneratedAxioms.literalRefutationCarrier
      𝗣𝗔 variableCarrier σ π d Γ).val/[(↑(formulaCode φ) : ArithmeticSemiterm Empty 0)] :
        ArithmeticSentence) := by
  let : 𝗥₀ ⪯ 𝗣𝗔 := WeakerThan.trans (𝓣 := 𝗣𝗔⁻) inferInstance inferInstance
  apply sigma_one_completeness (by simp)
  simpa [models_iff] using native_sentence_refutation σ π d Γ h hs

end CategoricalEssentialIncompleteness.V46.SyntacticNamedHilbert
