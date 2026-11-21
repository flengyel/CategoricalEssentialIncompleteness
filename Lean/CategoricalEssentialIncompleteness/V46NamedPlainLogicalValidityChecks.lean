/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedPlainLogicalValidity


/-! # Soundness of the constructed standard sentence derivations -/

@[expose] public section
noncomputable section
universe w
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.NamedPlainLogicalValidityChecks
open SyntacticSyntax NamedPostfixEncoding NamedPlainSemantics SyntacticGeneratedTheory
variable (σ π : ℕ → Carrier) (d : ℕ)
local notation "S" => plainCategoricalSyntax 𝗣𝗔 variableCarrier σ π d
local notation "G" => F 𝗣𝗔 ℕ
variable {K : Type w}
  (functions : ∀ n : Fin (d + 1), Symbols σ n.val → (Fin n.val → K) → K)
  (relations : ∀ n : Fin (d + 1), Symbols π n.val → (Fin n.val → K) → Prop)
example (l : Obj 𝗣𝗔 ℕ (S).logicalParameters) :
    Valid σ π d functions relations ((G).map (S).logicalAxioms l) :=
  valid_logicalAxioms σ π d functions relations l
end CategoricalEssentialIncompleteness.V46.NamedPlainLogicalValidityChecks
