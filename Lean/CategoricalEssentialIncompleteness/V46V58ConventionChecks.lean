/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryBooleanValuation
public import CategoricalEssentialIncompleteness.V46UniformTraceBuilders
public import CategoricalEssentialIncompleteness.ForkObstruction

/-! # Explicit checks of the conventions clarified in manuscript v58 -/

@[expose] public section
noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness

section BooleanValues
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D}

example : Two.point (C := D) true = (coprod.inr : ⊤_ D ⟶ Two D) := rfl
example : Two.point (C := D) false = (coprod.inl : ⊤_ D ⟶ Two D) := rfl

example (d : V46.DecidableVariables V) :
    IsPullback (prod.lift (𝟙 V) (𝟙 V)) (terminal.from V) d.test
      (coprod.inr : ⊤_ D ⟶ Two D) := d.diagonal

variable (S : V46.CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0)
variable (d : X ⟶ Two D)

example : S.quantifierConstructor ≫ V46.NullaryBooleanValuation.valuation S d =
    prod.snd ≫ V46.NullaryBooleanValuation.valuation S d :=
  V46.NullaryBooleanValuation.quantifier_value S d

example : S.equalityConstructor ≫ V46.NullaryBooleanValuation.valuation S d =
    Two.constant (S.algebra.a.1 ⨯ S.algebra.a.1) true :=
  V46.NullaryBooleanValuation.equality_value S d
end BooleanValues

example : ¬ Nonempty (LocalConnectedness.Fork.EqualityDecision LocalConnectedness.Fork.universal) :=
  LocalConnectedness.Fork.universal_no_decidable_equality

section TraceComposition
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition FailureOfComposition.ProofSearch FailureOfComposition.ConcreteEvaluator
open CategoricalRiceShapiro.Evaluator V46.UniformTrace

example : 𝗣𝗔 ⊢ compositionSentence := composition_PA

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝚺 1 := models_of_subtheory (U := 𝗣𝗔) inferInstance
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺 1) inferInstance

example (f e input output : M) :
    compositionTemplateGraph.val.Evalb ![⟪⟪f, e⟫, input⟫, output] ↔
      ∃ middle : M, graph.val.Evalb ![e, input, middle] ∧
        graph.val.Evalb ![f, middle, output] := by
  simpa only [pi₁_pair, pi₂_pair] using
    (compositionTemplateGraph_model (M := M) ⟪⟪f, e⟫, input⟫ output)
end TraceComposition

#print axioms V46.NullaryBooleanValuation.quantifier_value
#print axioms V46.NullaryBooleanValuation.equality_value
#print axioms LocalConnectedness.Fork.universal_no_decidable_equality
#print axioms V46.UniformTrace.compositionTemplateGraph_model
#print axioms V46.UniformTrace.composition_PA
