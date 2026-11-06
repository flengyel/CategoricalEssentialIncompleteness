/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46NamedPlainSemantics
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonSentences
import CategoricalEssentialIncompleteness.V46NamedPostfixFreeVariables

/-! # Validity on the actual standard sentence object -/

universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.NamedPlainSemantics
open SyntacticSyntax NamedPostfixEncoding ConcreteNamedComparison
variable (σ π : ℕ → Carrier) (d : ℕ)
local notation "S" => plainCategoricalSyntax 𝗣𝗔 variableCarrier σ π d
local notation "G" => F 𝗣𝗔 ℕ

/-- The formula obtained through the actual sentence inclusion is closed;
the pullback object's own raw value is not taken as a formula word. -/
theorem decode_sentence_closed (s : Obj 𝗣𝗔 ℕ (S).sentenceObject) :
    (decodeFormula σ π d ((G).map (S).sentenceInclusion s)).freeVariables = [] := by
  let word := (G).map (S).sentenceInclusion s
  have hs : (SyntacticSentenceImages.sentenceCarrier 𝗣𝗔 (S).sentenceInclusion).val.Evalb ![word.val] := by
    change (imageCarrier (chosenGraph 𝗣𝗔 (S).sentenceInclusion).graph).val.Evalb ![word.val]
    exact (imageCarrier_eval _ _).mpr
      ⟨s.val,(chosenGraph_map_iff 𝗣𝗔 ℕ (S).sentenceInclusion s word).mpr rfl⟩
  have hl := (sentenceCarrier_literal 𝗣𝗔 variableCarrier σ π d ℕ word.val).mp hs
  have hfv := ((literalSentenceCarrier_eval 𝗣𝗔 variableCarrier σ π d ℕ word.val).mp hl).2
  have hn := freeVariables_formulaCode (decodeFormula σ π d word)
  rw [decodeFormula_code] at hn
  exact (NamedPostfixEncoding.pack_eq_zero _).mp (hn.symm.trans hfv)

variable {K : Type w}
  (functions : ∀ n : Fin (d + 1), Symbols σ n.val → (Fin n.val → K) → K)
  (relations : ∀ n : Fin (d + 1), Symbols π n.val → (Fin n.val → K) → Prop)

/-- Sentence validity is a subset of the actual interpreted pullback
object, defined through its proved inclusion into formula syntax. -/
def validSentenceSet : Set (Obj 𝗣𝗔 ℕ (S).sentenceObject) :=
  {s | Valid σ π d functions relations ((G).map (S).sentenceInclusion s)}

/-- The intended negation-preimage intersection is empty on the actual
sentence object, for every nonempty semantic structure. -/
theorem sentence_validity_disjoint [Nonempty K] :
    Disjoint (validSentenceSet σ π d functions relations)
      ((fun s : Obj 𝗣𝗔 ℕ (S).sentenceObject => (G).map (S).sentenceNegation s) ⁻¹'
        validSentenceSet σ π d functions relations) := by
  rw [Set.disjoint_left]
  intro s hs hn
  change Valid σ π d functions relations ((G).map (S).sentenceInclusion s) at hs
  change Valid σ π d functions relations
    ((G).map (S).sentenceInclusion ((G).map (S).sentenceNegation s)) at hn
  have he := congrArg (fun f => (G).map f s) (S).sentenceNegation_inclusion
  rw [Functor.map_comp_apply,Functor.map_comp_apply] at he
  rw [he] at hn
  exact valid_negation_disjoint σ π d functions relations _ hs hn

end CategoricalEssentialIncompleteness.V46.NamedPlainSemantics
