/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionEquations

/-! Explicit PA-model and standard primitive-recursion statement checks. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding
open CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
example (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ) (formula : Bool) :
    𝗣𝗔 ⊢ freeVariablesConstructorSentence V σ π d formula :=
  freeVariables_constructor_PA V σ π d formula
example (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ) (formula : Bool) :
    𝗣𝗔 ⊢ substitutionConstructorSentence V σ π d formula :=
  substitution_constructor_PA V σ π d formula
