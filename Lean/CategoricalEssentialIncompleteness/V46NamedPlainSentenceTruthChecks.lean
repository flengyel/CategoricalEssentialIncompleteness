/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedPlainSentenceTruth


/-! # Truth of sentence codes is independent of the assignment -/

@[expose] public section
universe w
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.NamedPlainSentenceTruthChecks
open SyntacticSyntax NamedPostfixEncoding NamedPlainSemantics
variable (σ π : ℕ → Carrier) (d : ℕ)
local notation "S" => plainCategoricalSyntax 𝗣𝗔 variableCarrier σ π d
local notation "G" => F 𝗣𝗔 ℕ
example {K : Type w}
    (functions : ∀ n : Fin (d + 1), Symbols σ n.val → (Fin n.val → K) → K)
    (relations : ∀ n : Fin (d + 1), Symbols π n.val → (Fin n.val → K) → Prop)
    (s : Obj 𝗣𝗔 ℕ (S).sentenceObject) (ρ : ℕ → K) :
    Valid σ π d functions relations ((G).map (S).sentenceInclusion s) ↔
      Holds σ π d functions relations ((G).map (S).sentenceInclusion s) ρ :=
  sentence_valid_iff σ π d functions relations s ρ
end CategoricalEssentialIncompleteness.V46.NamedPlainSentenceTruthChecks
