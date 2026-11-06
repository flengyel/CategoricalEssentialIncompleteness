/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NamedArithmeticLiteralTotal
import CategoricalEssentialIncompleteness.V46NamedArithmeticProofSearchNegation
import CategoricalEssentialIncompleteness.V46SyntacticGeneratedRefutations
import CategoricalEssentialIncompleteness.V46NamedGammaSoundness
import CategoricalEssentialIncompleteness.V46LogicalComparison

/-! # The actual arithmetic sentence theory in literal model coordinates

The sentence carrier is the proved literal sentence predicate. The conclusion
and negation maps are transported by the existing constructor-preserving
sentence chart, so their image is the constructed Gamma theory.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists

namespace CategoricalEssentialIncompleteness.V46.ArithmeticLiteralModel
open NamedArithmeticSignature SyntacticSyntax

abbrev sentenceSyntax := plainCategoricalSyntax 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound
abbrev sentencePredicate : PredicateCategory 𝗣𝗔 := NamedArithmeticLiteralTotal.literalPredicate

def sentenceChart : CategoryTheory.Iso (C := PredicateCategory 𝗣𝗔)
    sentencePredicate sentenceSyntax.sentenceObject :=
  SyntacticSentenceLiteralChart.toSentenceIso 𝗣𝗔
    variableSymbols functionSymbols relationSymbols bound

def negation : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance
    sentencePredicate sentencePredicate :=
  sentenceChart.hom ≫ sentenceSyntax.sentenceNegation ≫ sentenceChart.inv

abbrev axiomObject (Γ : Carrier) : PredicateCategory 𝗣𝗔 :=
  SyntacticAxiomPredicates.axiomCarrier 𝗣𝗔
    variableSymbols functionSymbols relationSymbols bound Γ

abbrev axioms (Γ : Carrier) := SyntacticAxiomPredicates.axioms 𝗣𝗔
  variableSymbols functionSymbols relationSymbols bound Γ

abbrev formulaConclusion (Γ : Carrier) := SyntacticGeneratedTheory.conclusion 𝗣𝗔
  variableSymbols functionSymbols relationSymbols bound (axioms Γ)

abbrev proofObject (Γ : Carrier) : PredicateCategory 𝗣𝗔 :=
  SyntacticGeneratedTheory.sentenceProofObject 𝗣𝗔
    variableSymbols functionSymbols relationSymbols bound (axioms Γ)

def conclusion (Γ : Carrier) : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance
    (proofObject Γ) sentencePredicate :=
  SyntacticGeneratedTheory.sentenceConclusion 𝗣𝗔
    variableSymbols functionSymbols relationSymbols bound (axioms Γ) ≫ sentenceChart.inv

abbrev theoremPredicate (Γ : Carrier) := SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
  variableSymbols functionSymbols relationSymbols bound Γ

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local notation "G" => F 𝗣𝗔 M

theorem chart_inv_hom (s : Obj 𝗣𝗔 M sentencePredicate) :
    (G).map sentenceChart.inv ((G).map sentenceChart.hom s) = s := by
  have h := congrArg (fun f => (G).map f s) sentenceChart.hom_inv_id
  simpa only [Functor.map_comp_apply,Functor.map_id_apply] using h

theorem chart_hom_inv (s : Obj 𝗣𝗔 M sentenceSyntax.sentenceObject) :
    (G).map sentenceChart.hom ((G).map sentenceChart.inv s) = s := by
  have h := congrArg (fun f => (G).map f s) sentenceChart.inv_hom_id
  simpa only [Functor.map_comp_apply,Functor.map_id_apply] using h

theorem chart_value (s : Obj 𝗣𝗔 M sentencePredicate) :
    ((G).map sentenceSyntax.sentenceInclusion ((G).map sentenceChart.hom s)).val = s.val :=
  SyntacticSentenceLiteralChart.toSentence_value 𝗣𝗔
    variableSymbols functionSymbols relationSymbols bound M s

theorem chart_inv_value (s : Obj 𝗣𝗔 M sentenceSyntax.sentenceObject) :
    ((G).map sentenceChart.inv s).val = ((G).map sentenceSyntax.sentenceInclusion s).val := by
  have h := chart_value M ((G).map sentenceChart.inv s)
  rw [chart_hom_inv] at h
  exact h.symm

theorem negation_value (s : Obj 𝗣𝗔 M sentencePredicate) :
    ((G).map negation s).val = NamedArithmeticProofSearch.negationWord M s.val := by
  let u := (G).map sentenceChart.hom s
  rw [negation,Functor.map_comp_apply,Functor.map_comp_apply]
  change ((G).map sentenceChart.inv ((G).map sentenceSyntax.sentenceNegation u)).val = _
  rw [chart_inv_value]
  have h := SyntacticGeneratedAxioms.sentenceNegation_point 𝗣𝗔
    variableSymbols functionSymbols relationSymbols bound M u
  have he := (G).map_comp_apply sentenceSyntax.sentenceNegation sentenceSyntax.sentenceInclusion u
  rw [← he,h]
  rw [NamedPlainOperationsModels.negation_value]
  exact congrArg (NamedArithmeticProofSearch.negationWord M) (chart_value M s)

theorem conclusion_word (Γ : Carrier) (p : Obj 𝗣𝗔 M (proofObject Γ)) :
    ((G).map (conclusion Γ) p).val =
      ((G).map (SyntacticSentenceImages.restrictedConclusion 𝗣𝗔
        (formulaConclusion Γ) sentenceSyntax.sentenceInclusion) p).val := by
  let c := SyntacticGeneratedTheory.sentenceConclusion 𝗣𝗔
    variableSymbols functionSymbols relationSymbols bound (axioms Γ)
  let j := sentenceSyntax.sentenceInclusion
  have hl : ((G).map (conclusion Γ) p).val = ((G).map j ((G).map c p)).val :=
    (congrArg Subtype.val ((G).map_comp_apply c sentenceChart.inv p)).trans
      (chart_inv_value M ((G).map c p))
  have hr : ((G).map (SyntacticSentenceImages.restrictedConclusion 𝗣𝗔
      (formulaConclusion Γ) j) p).val = ((G).map j ((G).map c p)).val :=
    (congrArg Subtype.val ((G).map_comp_apply
      (pullback.snd (formulaConclusion Γ) j) (SyntacticSentenceImages.sentenceChart 𝗣𝗔 j).hom p)).trans
        (SyntacticSentenceImages.sentenceChart_value 𝗣𝗔 M j ((G).map c p))
  exact hl.trans hr.symm

/-- The actual Gamma program image uses the existing restricted-image
comparison, before choosing literal sentence coordinates. -/
theorem theorem_iff_image (Γ : Carrier) (s : Obj 𝗣𝗔 M sentencePredicate) :
    (theoremPredicate Γ).val.Evalb ![s.val] ↔
      ∃ p : Obj 𝗣𝗔 M (proofObject Γ), (G).map (conclusion Γ) p = s := by
  let j := sentenceSyntax.sentenceInclusion
  let c := formulaConclusion Γ
  let f := SyntacticSentenceImages.restrictedConclusion 𝗣𝗔 c j
  have h : (theoremPredicate Γ).val.Evalb ![s.val] ↔
      ∃ p : Obj 𝗣𝗔 M (proofObject Γ), ((G).map f p).val = s.val :=
    (SyntacticSentenceImages.programTheoryCarrier_theory 𝗣𝗔 c j M s.val).trans
      ((SyntacticSentenceImages.restrictedImage_eval 𝗣𝗔 M c j s.val).symm.trans
        (SyntacticGeneratedAxioms.imageCarrier_points 𝗣𝗔 M f s.val))
  apply h.trans
  constructor
  · rintro ⟨p,hp⟩
    exact ⟨p,Subtype.ext ((conclusion_word M Γ p).trans hp)⟩
  · rintro ⟨p,hp⟩
    exact ⟨p,(conclusion_word M Γ p).symm.trans (congrArg Subtype.val hp)⟩

def thetaPoint (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) (n : M) :
    Obj 𝗣𝗔 M sentencePredicate :=
  ⟨NamedArithmeticFixedSubstitution.value φ n,
    NamedArithmeticFixedSubstitution.value_sentence (M := M) φ hφ n⟩


theorem thetaPoint_value (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) (n : M) :
    (thetaPoint M φ hφ n).val = NamedArithmeticFixedSubstitution.value φ n := rfl

end Models
end CategoricalEssentialIncompleteness.V46.ArithmeticLiteralModel
