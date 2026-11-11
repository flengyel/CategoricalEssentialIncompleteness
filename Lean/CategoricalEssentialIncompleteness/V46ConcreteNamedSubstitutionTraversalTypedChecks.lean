/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionTraversalTyped

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
example (a b : RawPolynomial) (F G : 𝚺₁.Semisentence 3) (f g : M → M → M)
    [𝚺₁-Function₂ f via F] [𝚺₁-Function₂ g via G] (param : M) (X Y : Carrier)
    (ht : ∀ u : M,(rawCarrier X Y a).val.Evalb ![u] → X.val.Evalb ![f param u])
    (hf : ∀ u : M,(rawCarrier X Y b).val.Evalb ![u] → Y.val.Evalb ![g param u])
    (formula : Bool) (word : M) (h : (Postfix.carrier formula a b).val.Evalb ![word]) :
    (if formula then Y else X).val.Evalb ![Traversal.output a b F G f g param word] :=
  Traversal.output_typed a b F G f g param X Y ht hf formula word h
