/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NamedPlainSentenceSemantics

/-! # Truth of sentence codes is independent of the assignment -/

@[expose] public section

universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.NamedPlainSemantics
open SyntacticSyntax NamedPostfixEncoding
variable (σ π : ℕ → Carrier) (d : ℕ)
local notation "S" => plainCategoricalSyntax 𝗣𝗔 variableCarrier σ π d
local notation "G" => F 𝗣𝗔 ℕ
variable {K : Type w}
  (functions : ∀ n : Fin (d + 1), Symbols σ n.val → (Fin n.val → K) → K)
  (relations : ∀ n : Fin (d + 1), Symbols π n.val → (Fin n.val → K) → Prop)

theorem holds_sentence_congr (s : Obj 𝗣𝗔 ℕ (S).sentenceObject) (ρ τ : ℕ → K) :
    Holds σ π d functions relations ((G).map (S).sentenceInclusion s) ρ ↔
      Holds σ π d functions relations ((G).map (S).sentenceInclusion s) τ := by
  apply NamedFiniteSyntax.Formula.holds_congr
  intro x hx
  rw [decode_sentence_closed] at hx
  exact (List.not_mem_nil hx).elim

/-- On the sentence inclusion, validity is truth at any chosen assignment. Thus the
validity factor uses sentence satisfaction. -/
theorem sentence_valid_iff (s : Obj 𝗣𝗔 ℕ (S).sentenceObject) (ρ : ℕ → K) :
    Valid σ π d functions relations ((G).map (S).sentenceInclusion s) ↔
      Holds σ π d functions relations ((G).map (S).sentenceInclusion s) ρ := by
  constructor
  · exact fun h => h ρ
  · exact fun h τ => (holds_sentence_congr σ π d functions relations s ρ τ).mp h

/-- Satisfaction of the nonlogical sentence axioms at one assignment
gives the validity hypothesis used by standard rule induction. -/
theorem axioms_valid_of_holds {A : PredicateCategory 𝗣𝗔} (axioms : A ⟶ (S).sentenceObject)
    (ρ : ℕ → K)
    (h : ∀ a : Obj 𝗣𝗔 ℕ A,
      Holds σ π d functions relations ((G).map (axioms ≫ (S).sentenceInclusion) a) ρ) :
    ∀ a : Obj 𝗣𝗔 ℕ A,
      Valid σ π d functions relations ((G).map (axioms ≫ (S).sentenceInclusion) a) := by
  intro a
  rw [Functor.map_comp_apply]
  exact (sentence_valid_iff σ π d functions relations ((G).map axioms a) ρ).mpr
    (by simpa only [Functor.map_comp_apply] using h a)

end CategoricalEssentialIncompleteness.V46.NamedPlainSemantics
