/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralDomainValues
import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralSentences
import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralDecoding
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonSentences

/-! # The numerical sentence pullback has exactly the closed named words -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalNamed

variable (V : NumericalTuples.Object) (σ π : ℕ → NumericalTuples.Object) (d : ℕ)
local notation "E" => literalEquivalence
local notation "S₀" => literalSourceSyntax V σ π d
local notation "S₁" => literalCategoricalSyntax V σ π d
local notation "V₀" => NumericalCoordinates.codedPredicate V
local notation "σ₀" => (fun n => NumericalCoordinates.codedPredicate (σ n))
local notation "π₀" => (fun n => NumericalCoordinates.codedPredicate (π n))

def literalSentencePresentationIso : (S₁).sentenceObject ≅
    NumericalCoordinates.predicateObject (S₀).sentenceObject :=
  (literalSentenceIso V σ π d).symm ≪≫
    NumericalCoordinates.predicatePresentationIso (S₀).sentenceObject

theorem literal_sentenceInclusion_code_square :
    (S₁).sentenceInclusion ≫ (literalFormulaPresentationIso V σ π d).hom =
      (literalSentencePresentationIso V σ π d).hom ≫
        NumericalCoordinates.predicateMap (S₀).sentenceInclusion :=
  conjugate_operation ((E).functor.map (S₀).sentenceInclusion) (S₁).sentenceInclusion
    (literalSentenceIso V σ π d) (literalFormulaIso V σ π d)
    (NumericalCoordinates.predicatePresentationIso (S₀).sentenceObject)
    (NumericalCoordinates.predicatePresentationIso (S₀).algebra.a.2)
    (literalSentenceIso_inclusion V σ π d).symm

private theorem source_sentence_image_iff
    (w : PredicateInterpretation.Obj ℕ (S₀).algebra.a.2) :
    (∃ s, (PredicateInterpretation.functor 𝗧𝗔 ℕ).map (S₀).sentenceInclusion s = w) ↔
      ConcreteNamedSubstitution.freeVariables (M := ℕ) V₀ σ₀ π₀ d w.val = 0 := by
  let G := chosenGraph 𝗧𝗔 (S₀).sentenceInclusion
  constructor
  · rintro ⟨s, hs⟩
    have hg := (SyntacticLists.chosenGraph_map_iff 𝗧𝗔 ℕ (S₀).sentenceInclusion s w).mpr hs
    have hi : (SyntacticSentenceImages.sentenceCarrier 𝗧𝗔 (S₀).sentenceInclusion).val.Evalb ![w.val] :=
      (imageCarrier_eval G.graph w.val).mpr ⟨s.val, hg⟩
    exact ((ConcreteNamedComparison.literalSentenceCarrier_eval 𝗧𝗔 V₀ σ₀ π₀ d ℕ w.val).mp
      ((ConcreteNamedComparison.sentenceCarrier_literal 𝗧𝗔 V₀ σ₀ π₀ d ℕ w.val).mp hi)).2
  · intro hv
    have hl : (ConcreteNamedComparison.literalSentenceCarrier 𝗧𝗔 V₀ σ₀ π₀ d).val.Evalb ![w.val] :=
      (ConcreteNamedComparison.literalSentenceCarrier_eval 𝗧𝗔 V₀ σ₀ π₀ d ℕ w.val).mpr ⟨w.property, hv⟩
    have hi := (ConcreteNamedComparison.sentenceCarrier_literal 𝗧𝗔 V₀ σ₀ π₀ d ℕ w.val).mpr hl
    obtain ⟨s, hs⟩ := (imageCarrier_eval G.graph w.val).mp hi
    let ss : PredicateInterpretation.Obj ℕ (S₀).sentenceObject :=
      ⟨s, (G.support_model ℕ s w.val hs).1⟩
    exact ⟨ss, (SyntacticLists.chosenGraph_map_iff 𝗧𝗔 ℕ (S₀).sentenceInclusion ss w).mp hs⟩

theorem literal_sentence_iff (w : NumericalTuples.Point (S₁).algebra.a.2) :
    (∃ s, (S₁).sentenceInclusion.toFun s = w) ↔
      ConcreteNamedSubstitution.freeVariables (M := ℕ) V₀ σ₀ π₀ d
        ((literalFormulaPresentationIso V σ π d).hom.toFun w).val = 0 := by
  refine (numerical_image_chart (S₁).sentenceInclusion
    (NumericalCoordinates.predicateMap (S₀).sentenceInclusion)
    (literalSentencePresentationIso V σ π d) (literalFormulaPresentationIso V σ π d)
    (literal_sentenceInclusion_code_square V σ π d) w).trans ?_
  have hp := source_sentence_image_iff V σ π d
    ((literalFormulaPresentationIso V σ π d).hom.toFun w)
  constructor
  · rintro ⟨x, hx⟩
    exact hp.mp ⟨x, (NumericalCoordinates.predicateMap_value (S₀).sentenceInclusion x).symm.trans hx⟩
  · intro h
    obtain ⟨x, hx⟩ := hp.mpr h
    exact ⟨x, (NumericalCoordinates.predicateMap_value (S₀).sentenceInclusion x).trans hx⟩

theorem literal_sentence_decodes (s : NumericalTuples.Point
    (literalCategoricalSyntax variableObject σ π d).sentenceObject) :
    ∃ φ : NamedFiniteSyntax.Formula (NamedPostfixEncoding.Symbols σ₀)
        (NamedPostfixEncoding.Symbols π₀) d,
      φ.freeVariables = [] ∧ NamedPostfixEncoding.formulaCode φ =
        ((literalFormulaPresentationIso variableObject σ π d).hom.toFun
          ((literalCategoricalSyntax variableObject σ π d).sentenceInclusion.toFun s)).val := by
  let w := (literalCategoricalSyntax variableObject σ π d).sentenceInclusion.toFun s
  obtain ⟨φ, hφ⟩ := literal_formula_decodes σ π d w
  refine ⟨φ, ?_, hφ⟩
  apply (NamedPostfixEncoding.sentence_formulaCode_iff φ).mp
  have hw := (literal_sentence_iff variableObject σ π d w).mp ⟨s, rfl⟩
  exact (freeVariables_variable_parameter (NumericalCoordinates.codedPredicate variableObject)
    NamedPostfixEncoding.variableCarrier σ₀ π₀ d (NamedPostfixEncoding.formulaCode φ)).symm.trans
      ((congrArg (ConcreteNamedSubstitution.freeVariables (M := ℕ)
        (NumericalCoordinates.codedPredicate variableObject) σ₀ π₀ d) hφ).trans hw)

end CategoricalEssentialIncompleteness.V46.NumericalNamed
