/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionLists

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
example (x y list : M) : member x (delete y list) = if x = y then 0 else member x list :=
  member_delete x y list
example (V : Carrier) (x list : M) (h : (SyntacticLists.listCarrier V).val.Evalb ![list]) :
    (SyntacticLists.listCarrier V).val.Evalb ![delete x list] := delete_carrier V x list h
example : Primrec₂ (delete : ℕ → ℕ → ℕ) := delete_primrec
example : Primrec₂ (member : ℕ → ℕ → ℕ) := member_primrec
