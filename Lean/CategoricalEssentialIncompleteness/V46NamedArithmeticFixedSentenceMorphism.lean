/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedArithmeticFixedSubstitution
public import CategoricalEssentialIncompleteness.V46SyntacticSentenceLiteralChart

/-! The complete sentence-morphism construction for a generic finite
named formula with its external free-name bound. Later specializations
apply these theorems without reducing any selected arithmetic index. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
namespace CategoricalEssentialIncompleteness.V46.NamedArithmeticFixedSentenceMorphism
open NamedArithmeticSignature NamedArithmeticFixedSubstitution

 def theta (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) :
    @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance variableSymbols
      (plainCategoricalSyntax 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound).sentenceObject :=
  representedArrow 𝗣𝗔 (morphism φ hφ) ≫
    SyntacticSentenceLiteralChart.toSentence 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound

 theorem theta_inclusion (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) :
    theta φ hφ ≫ (plainCategoricalSyntax 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound).sentenceInclusion =
      representedArrow 𝗣𝗔 (morphism φ hφ) ≫
        SyntacticSentenceLiteralChart.toImage 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound ≫
          SyntacticSentenceLiteralChart.imageInclusion 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound := by
  rw [theta,Category.assoc,SyntacticSentenceLiteralChart.toSentence_over]

 theorem theta_unique (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0)
    (g : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance variableSymbols
      (plainCategoricalSyntax 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound).sentenceObject)
    (hg : g ≫ (plainCategoricalSyntax 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound).sentenceInclusion =
      representedArrow 𝗣𝗔 (morphism φ hφ) ≫
        SyntacticSentenceLiteralChart.toImage 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound ≫
          SyntacticSentenceLiteralChart.imageInclusion 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound) : g = theta φ hφ := by
  apply (cancel_mono (plainCategoricalSyntax 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound).sentenceInclusion).mp
  exact hg.trans (theta_inclusion φ hφ).symm

 theorem morphism_value (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (n : PredicateInterpretation.Obj M variableSymbols) :
    ((PredicateInterpretation.functor 𝗣𝗔 M).map (representedArrow 𝗣𝗔 (morphism φ hφ)) n).val = value φ n.val := by
  have hg := (PredicateInterpretation.map_class_eq_iff 𝗣𝗔 M (morphism φ hφ) n
    ((PredicateInterpretation.functor 𝗣𝗔 M).map (representedArrow 𝗣𝗔 (morphism φ hφ)) n)).mp rfl
  exact (morphism_graph_eval (M := M) φ hφ n.val _).mp hg

 theorem theta_word_value (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (n : PredicateInterpretation.Obj M variableSymbols) :
    ((PredicateInterpretation.functor 𝗣𝗔 M).map
      (plainCategoricalSyntax 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound).sentenceInclusion
      ((PredicateInterpretation.functor 𝗣𝗔 M).map (theta φ hφ) n)).val = value φ n.val := by
  rw [theta,Functor.map_comp_apply]
  exact (SyntacticSentenceLiteralChart.toSentence_value 𝗣𝗔 variableSymbols functionSymbols relationSymbols bound M
    ((PredicateInterpretation.functor 𝗣𝗔 M).map (representedArrow 𝗣𝗔 (morphism φ hφ)) n)).trans
      (morphism_value φ hφ M n)

end CategoricalEssentialIncompleteness.V46.NamedArithmeticFixedSentenceMorphism
