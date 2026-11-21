/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticAxiomPredicates


/-! # The concrete sentence-axiom subobject of a Sigma-one enumeration -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.SyntacticAxiomPredicatesChecks
open SyntacticSyntax SyntacticAxiomPredicates ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ) (Γ : Carrier)
example : Mono (axioms T V σ π d Γ) := inferInstance
example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (word : M) :
    (axiomCarrier T V σ π d Γ).val.Evalb ![word] ↔
      Γ.val.Evalb ![word] ∧ (literalSentenceCarrier T V σ π d).val.Evalb ![word] :=
  axiomCarrier_literal T V σ π d M Γ word
example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (word : M) :
    (imageCarrier (chosenGraph T (axioms T V σ π d Γ ≫
      (plainCategoricalSyntax T V σ π d).sentenceInclusion)).graph).val.Evalb ![word] ↔
      Γ.val.Evalb ![word] ∧ (literalSentenceCarrier T V σ π d).val.Evalb ![word] :=
  axioms_formula_image T V σ π d M Γ word
example : T ⊢ axiomCarrierLiteralSentence T V σ π d Γ := axiomCarrier_literal_theory T V σ π d Γ
end CategoricalEssentialIncompleteness.V46.SyntacticAxiomPredicatesChecks
