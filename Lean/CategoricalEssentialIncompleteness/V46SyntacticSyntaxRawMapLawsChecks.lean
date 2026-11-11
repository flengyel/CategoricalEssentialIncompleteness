/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxRawMapLaws

/-! # Explicit signature checks for RawMapLaws -/

@[expose] public section

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

example (P : Carrier) (ht hf et ef : TernaryGraph)
    (h₁ : ∀ p u v : M, ht.val.Evalb ![p,u,v] ↔ et.val.Evalb ![p,u,v])
    (h₂ : ∀ p u v : M, hf.val.Evalb ![p,u,v] ↔ ef.val.Evalb ![p,u,v])
    (a : RawPolynomial) (p u v : M) :
    (mapRaw P ht hf a).val.Evalb ![p,u,v] ↔
      (mapRaw P et ef a).val.Evalb ![p,u,v] := mapRaw_congr_model P ht hf et ef h₁ h₂ a p u v
