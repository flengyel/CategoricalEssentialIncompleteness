/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonPlainOccurrences
import CategoricalEssentialIncompleteness.V46SyntacticGeneratedTheory
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-! # Literal sentence codes are precisely plain formula codes with empty FV -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)

/-- Both conjuncts concern the same literal formula word. The graph is
that of the actual PA-total numerical free-variable traversal. -/
def literalSentenceCarrier : Carrier :=
  let C := Postfix.plainCarrier true (SyntaxPolynomial.termExpression V σ d)
    (SyntaxPolynomial.formulaExpression V π d)
  let G := ConcreteNamedSubstitution.freeVariablesGraph V σ π d
  .mkSigma “word. !C.val word ∧ !G.val 0 word”

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

omit [𝗣𝗔 ⪯ T] [M↓[ℒₒᵣ] ⊧* T] in
@[simp] theorem literalSentenceCarrier_eval (word : M) :
    (literalSentenceCarrier T V σ π d).val.Evalb ![word] ↔
      (Postfix.plainCarrier true (SyntaxPolynomial.termExpression V σ d)
        (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![word] ∧
          ConcreteNamedSubstitution.freeVariables V σ π d word = 0 := by
  simp [literalSentenceCarrier,eq_comm]

/-- The chosen pullback object need not itself use formula coordinates;
its actual inclusion has exactly this numeric image. -/
theorem sentenceCarrier_literal (word : M) :
    (SyntacticSentenceImages.sentenceCarrier T
      (plainCategoricalSyntax T V σ π d).sentenceInclusion).val.Evalb ![word] ↔
        (literalSentenceCarrier T V σ π d).val.Evalb ![word] := by
  let S := plainCategoricalSyntax T V σ π d
  rw [literalSentenceCarrier_eval]
  change (imageCarrier (chosenGraph T S.sentenceInclusion).graph).val.Evalb ![word] ↔ _
  rw [imageCarrier_eval]
  constructor
  · rintro ⟨s,hs⟩
    let ss : Obj T M S.sentenceObject :=
      ⟨s,((chosenGraph T S.sentenceInclusion).support_model M s word hs).1⟩
    let ww : Obj T M S.algebra.a.2 :=
      ⟨word,((chosenGraph T S.sentenceInclusion).support_model M s word hs).2⟩
    have he : (F T M).map S.sentenceInclusion ss = ww :=
      (chosenGraph_map_iff T M S.sentenceInclusion ss ww).mp hs
    let q := (F T M).map (pullback.snd S.formulaOccurrences S.lists.algebra.nil) ss
    have hp : (F T M).map S.formulaOccurrences ww = (F T M).map S.lists.algebra.nil q := by
      have h := congrArg (fun f => (F T M).map f ss)
        (pullback.condition (f := S.formulaOccurrences) (g := S.lists.algebra.nil))
      change (F T M).map (S.sentenceInclusion ≫ S.formulaOccurrences) ss =
        (F T M).map (pullback.snd S.formulaOccurrences S.lists.algebra.nil ≫ S.lists.algebra.nil) ss at h
      rw [Functor.map_comp_apply,Functor.map_comp_apply] at h
      exact (congrArg ((F T M).map S.formulaOccurrences) he).symm.trans h
    have hv := congrArg Subtype.val hp
    have hn := nil_value T M _ V q
    have ho := plain_formulaOccurrences_value T V σ π d M ww
    exact ⟨ww.property,ho.symm.trans (hv.trans hn)⟩
  · rintro ⟨hw,hv⟩
    let ww : Obj T M S.algebra.a.2 := ⟨word,hw⟩
    let q := modelTerminalPoint T M
    have hp : (F T M).map S.formulaOccurrences ww = (F T M).map S.lists.algebra.nil q := by
      apply Subtype.ext
      exact (plain_formulaOccurrences_value T V σ π d M ww).trans
        (hv.trans (nil_value T M _ V q).symm)
    obtain ⟨ss,hf,_⟩ := Types.exists_of_isPullback
      ((F T M).map_isPullback (IsPullback.of_hasPullback S.formulaOccurrences S.lists.algebra.nil)) ww q hp
    exact ⟨ss.val,(chosenGraph_map_iff T M S.sentenceInclusion ss ww).mpr hf⟩

end Models

/-- This is a literal T-proof of the intended numerical sentence
predicate, derived after identifying the actual occurrence fold. -/
def sentenceCarrierLiteralSentence : ArithmeticSentence :=
  let C := SyntacticSentenceImages.sentenceCarrier T
    (plainCategoricalSyntax T V σ π d).sentenceInclusion
  let D := literalSentenceCarrier T V σ π d
  “∀ word, !C.val word ↔ !D.val word”

theorem sentenceCarrier_literal_theory : T ⊢ sentenceCarrierLiteralSentence T V σ π d := by
  apply complete.{0} T
  intro M _ _
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  simpa [models_iff,sentenceCarrierLiteralSentence] using
    (fun word : M => sentenceCarrier_literal T V σ π d M word)

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
