/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkFirstOrderErasure
public import CategoricalEssentialIncompleteness.V46ForkPropositionalFolds
public import CategoricalEssentialIncompleteness.V46NullaryLogicalPoint
public import CategoricalEssentialIncompleteness.V46NullarySyntaxOccurrences

/-! # The propositional sentence embedding and its erasure retraction -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ForkPropositionalEmbedding
open ForkDerivation.Diagram ForkFirstOrderErasure
local notation "S" => firstOrder

def sentenceImplication : (S).sentenceObject ⨯ (S).sentenceObject ⟶ (S).sentenceObject :=
  pullback.lift (prod.map (S).sentenceInclusion (S).sentenceInclusion ≫
    (S).implicationConstructor) (terminal.from _) (by
      have h : prod.map (S).sentenceInclusion (S).sentenceInclusion =
          prod.lift (prod.fst ≫ (S).sentenceInclusion)
            (prod.snd ≫ (S).sentenceInclusion) := by
        apply prod.hom_ext <;> simp
      rw [h]
      change (prod.lift (prod.fst ≫ (S).sentenceInclusion)
        (prod.snd ≫ (S).sentenceInclusion) ≫ (S).implicationConstructor) ≫
          (S).formulaOccurrences = _
      apply NullaryLogicalPoint.implication_closed
      all_goals rw [Category.assoc, NullaryInterpretation.sentence_occurrences,
        ← Category.assoc, terminal.comp_from])

@[reassoc] theorem sentenceImplication_inclusion :
    sentenceImplication ≫ (S).sentenceInclusion =
      prod.map (S).sentenceInclusion (S).sentenceInclusion ≫ (S).implicationConstructor :=
  pullback.lift_fst _ _ _

/-- The fold lands in the sentence pullback, rather than only in formulas. -/
def embedding : sentences ⟶ (S).sentenceObject := ForkPropositionalFolds.fold _
  (NullaryInterpretation.atomSentence (S)) (S).sentenceNegation sentenceImplication

@[reassoc] theorem atom : ForkFirstOrderErasure.atom ≫ embedding =
    NullaryInterpretation.atomSentence (S) := ForkPropositionalFolds.fold_atom _ _ _ _

@[reassoc] theorem negation : ForkFirstOrderErasure.negation ≫ embedding =
    embedding ≫ (S).sentenceNegation := ForkPropositionalFolds.fold_negation _ _ _ _

@[reassoc] theorem implication : ForkDerivation.Diagram.implication ≫ embedding =
    prod.map embedding embedding ≫ sentenceImplication :=
  ForkPropositionalFolds.fold_implication _ _ _ _

def formulaEmbedding : sentences ⟶ formulas := embedding ≫ (S).sentenceInclusion

@[reassoc] theorem formula_atom : ForkFirstOrderErasure.atom ≫ formulaEmbedding =
    NullaryInterpretation.atomFormula (S) := by
  rw [formulaEmbedding, ← Category.assoc, atom, NullaryInterpretation.atomSentence_inclusion]

@[reassoc] theorem formula_negation : ForkFirstOrderErasure.negation ≫ formulaEmbedding =
    formulaEmbedding ≫ (S).negationConstructor := by
  rw [formulaEmbedding, ← Category.assoc, negation, Category.assoc,
    CategoricalSyntax.sentenceNegation_inclusion, ← Category.assoc]

@[reassoc] theorem formula_implication :
    ForkDerivation.Diagram.implication ≫ formulaEmbedding =
      prod.map formulaEmbedding formulaEmbedding ≫ (S).implicationConstructor := by
  rw [formulaEmbedding, ← Category.assoc, implication, Category.assoc,
    sentenceImplication_inclusion, ← Category.assoc, prod.map_map]

/-- The retraction equation, with the original propositional carrier. -/
theorem retraction : embedding ≫ (S).sentenceInclusion ≫ erase = 𝟙 sentences := by
  have h : formulaEmbedding ≫ erase = ForkPropositionalFolds.fold sentences
      ForkFirstOrderErasure.atom ForkFirstOrderErasure.negation
      ForkDerivation.Diagram.implication := by
    apply ForkPropositionalFolds.unique
    · change ForkFirstOrderErasure.atom ≫ formulaEmbedding ≫ erase = _
      rw [← Category.assoc, formula_atom, atom_law]
    · change ForkFirstOrderErasure.negation ≫ formulaEmbedding ≫ erase = _
      rw [← Category.assoc, formula_negation, Category.assoc, negation_law,
        ← Category.assoc]
    · rw [← Category.assoc, formula_implication, Category.assoc, implication_law,
        ← Category.assoc, prod.map_map]
  have hi : 𝟙 sentences = ForkPropositionalFolds.fold sentences
      ForkFirstOrderErasure.atom ForkFirstOrderErasure.negation
      ForkDerivation.Diagram.implication := ForkPropositionalFolds.unique _ _ _ _ _
        (Category.comp_id _)
        (by
          change ForkFirstOrderErasure.negation ≫ 𝟙 sentences =
            𝟙 sentences ≫ ForkFirstOrderErasure.negation
          simp only [Category.comp_id, Category.id_comp]) (by simp)
  change formulaEmbedding ≫ erase = 𝟙 sentences
  exact h.trans hi.symm

instance embedding_mono : Mono embedding := by
  exact ⟨fun f g he => by
    have he' := congrArg (fun m => m ≫ (S).sentenceInclusion ≫ erase) he
    simpa only [Category.assoc, retraction, Category.comp_id] using he'⟩

theorem naturality {j k : CategoryTheory.Limits.WalkingSpan}
    (f : j ⟶ k) : sentences.map f ≫ embedding.app k =
      embedding.app j ≫ (S).sentenceObject.map f := embedding.naturality f

end CategoricalEssentialIncompleteness.V46.ForkPropositionalEmbedding
