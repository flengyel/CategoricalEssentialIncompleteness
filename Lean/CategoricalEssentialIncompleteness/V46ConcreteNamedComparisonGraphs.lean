/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionFreeVariables
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxInitial
public import CategoricalEssentialIncompleteness.V46CategoricalFreeVariables

/-! # Quotient morphisms for the numerical occurrence traversal -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open FailureOfComposition.ProofSearch
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison

def syntaxCarrier (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ) (formula : Bool) : Carrier :=
  SyntacticSyntax.Postfix.carrier formula (SyntaxPolynomial.termExpression V σ d)
    (SyntaxPolynomial.formulaExpression V π d)

/-- Source restriction is explicit; the raw algorithm remains a total
numerical function even on words outside the syntax predicate. -/
def occurrencesGraph (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ) (formula : Bool) : Graph :=
  let C := syntaxCarrier V σ π d formula
  let G := ConcreteNamedSubstitution.freeVariablesGraph V σ π d
  .mkSigma “word out. !C.val word ∧ !G.val out word”

section ArithmeticModels
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

@[simp] theorem occurrencesGraph_eval (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ)
    (formula : Bool) (word out : M) :
    (occurrencesGraph V σ π d formula).val.Evalb ![word,out] ↔
      (syntaxCarrier V σ π d formula).val.Evalb ![word] ∧
        out = ConcreteNamedSubstitution.freeVariables V σ π d word := by
  simp [occurrencesGraph]

end ArithmeticModels

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)

/-- This is a constructed graph morphism, using PA carrier preservation of the traversal,
rather than an evaluator supplied as data. -/
def occurrencesMorphism (formula : Bool) :
    GraphMorphism T (syntaxCarrier V σ π d formula) (listObject T V) where
  graph := occurrencesGraph V σ π d formula
  support := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff, SyntacticPredicates.supportSentence_eval]
    intro word out h
    obtain ⟨hw, rfl⟩ := (occurrencesGraph_eval V σ π d formula word out).mp h
    exact ⟨hw, ConcreteNamedSubstitution.freeVariables_carrier V σ π d formula word hw⟩
  total := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff, totalSentence_eval]
    intro word hw
    refine ⟨ConcreteNamedSubstitution.freeVariables V σ π d word,
      (occurrencesGraph_eval V σ π d formula word _).mpr ⟨hw,rfl⟩, ?_⟩
    intro out hout
    exact ((occurrencesGraph_eval V σ π d formula word out).mp hout).2

def occurrencesArrow (formula : Bool) :
    @Quiver.Hom (PredicateCategory T) inferInstance (syntaxCarrier V σ π d formula) (listObject T V) :=
  representedArrow T (occurrencesMorphism T V σ π d formula)

theorem occurrencesArrow_value (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
    [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (formula : Bool) (word : Obj T M (syntaxCarrier V σ π d formula)) :
    ((F T M).map (occurrencesArrow T V σ π d formula) word).val =
      ConcreteNamedSubstitution.freeVariables V σ π d word.val := by
  let f := occurrencesMorphism T V σ π d formula
  let out := (F T M).map (occurrencesArrow T V σ π d formula) word
  have h := (PredicateInterpretation.map_class_eq_iff T M f word out).mp rfl
  exact ((occurrencesGraph_eval V σ π d formula word.val out.val).mp h).2

/-- The two numerical candidates have the exact target carriers of the
categorical occurrence algebra on canonical postfix syntax. -/
def occurrencesPair :
    (SyntacticSyntax.categoricalSyntax T V σ π d).algebra.a ⟶
      (SyntacticSyntax.categoricalSyntax T V σ π d).occurrenceAlgebra.a :=
  (occurrencesArrow T V σ π d false, occurrencesArrow T V σ π d true)

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
