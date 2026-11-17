/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkPropositionalEmbedding

/-! # Independent checks of the embedding and erasure in Proposition 10.8

These check the syntax comparison. Conservativity, admissible substitution,
consistency and the incompleteness conclusions remain separate obligations.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkErasureStatementChecks
open ForkDerivation.Diagram ForkFirstOrderErasure

example : labels = realization.obj ForkDerivation.variableObject := rfl
example : sentences = realization.obj ForkDerivation.sentenceObject := rfl
example : ForkDerivation.variableObject.obj = EffectiveFork.V := rfl
example : atom = realization.map ForkDerivation.atom := rfl
example : negation = realization.map ForkDerivation.negation := rfl
example : implication = inv (prodComparison realization ForkDerivation.sentenceObject
    ForkDerivation.sentenceObject) ≫ realization.map ForkDerivation.implication := rfl

example : EffectiveFork.quadCode (0, 0, 0, 0) = 0 := rfl
example : EffectiveFork.leftCoordinate 0 = Nat.pair 0 0 := rfl
example : EffectiveFork.rightCoordinate 0 = Nat.pair 0 0 := rfl
example : isTotal zeroArrow := zeroArrow_total

example (x y : ℕ) : y ∈ EnumerableCarriers.val zeroArrow.center x ↔
    x ∈ (⊤_ EffectiveFork.Total).obj.center.support ∧ y = 0 :=
  EnumerableCarriers.mem_totalFromFunction (fun _ => 0) (.const 0)
    (fun _ _ => Set.mem_univ _) x y
example (x y : ℕ) : y ∈ EnumerableCarriers.val zeroArrow.left x ↔
    x ∈ (⊤_ EffectiveFork.Total).obj.left.support ∧ y = 0 :=
  EnumerableCarriers.mem_totalFromFunction (fun _ => 0) (.const 0)
    (fun _ _ => Set.mem_univ _) x y
example (x y : ℕ) : y ∈ EnumerableCarriers.val zeroArrow.right x ↔
    x ∈ (⊤_ EffectiveFork.Total).obj.right.support ∧ y = 0 :=
  EnumerableCarriers.mem_totalFromFunction (fun _ => 0) (.const 0)
    (fun _ _ => Set.mem_univ _) x y

example : zeroPoint = inv (terminalComparison realization) ≫
    realization.map ⟨zeroArrow, zeroArrow_total⟩ := rfl
example : truth = prod.lift (zeroPoint ≫ atom) (zeroPoint ≫ atom) ≫ implication := rfl

example : firstOrder.equalityConstructor ≫ erase = terminal.from _ ≫ truth := equality
example : NullaryInterpretation.atomFormula firstOrder ≫ erase = atom := atom_law
example : firstOrder.negationConstructor ≫ erase = erase ≫ negation := negation_law
example : firstOrder.implicationConstructor ≫ erase = prod.map erase erase ≫ implication :=
  implication_law
example : firstOrder.quantifierConstructor ≫ erase = prod.snd ≫ erase := quantifier

/-- No monicity or atom-equality reflection assumption appears. -/
example {j k : WalkingSpan} (f : j ⟶ k) :
    formulas.map f ≫ erase.app k = erase.app j ≫ sentences.map f := naturality f

example (m : formulas ⟶ sentences)
    (he : firstOrder.equalityConstructor ≫ m = terminal.from _ ≫ truth)
    (ha : NullaryInterpretation.atomFormula firstOrder ≫ m = atom)
    (hn : firstOrder.negationConstructor ≫ m = m ≫ negation)
    (hi : firstOrder.implicationConstructor ≫ m = prod.map m m ≫ implication)
    (hq : firstOrder.quantifierConstructor ≫ m = prod.snd ≫ m) : m = erase :=
  unique m he ha hn hi hq

open ForkPropositionalEmbedding (embedding sentenceImplication)

example : atom ≫ embedding = NullaryInterpretation.atomSentence firstOrder :=
  ForkPropositionalEmbedding.atom
example : negation ≫ embedding = embedding ≫ firstOrder.sentenceNegation :=
  ForkPropositionalEmbedding.negation
example : implication ≫ embedding = prod.map embedding embedding ≫ sentenceImplication :=
  ForkPropositionalEmbedding.implication
example : sentenceImplication ≫ firstOrder.sentenceInclusion =
    prod.map firstOrder.sentenceInclusion firstOrder.sentenceInclusion ≫
      firstOrder.implicationConstructor := ForkPropositionalEmbedding.sentenceImplication_inclusion
example : embedding ≫ firstOrder.sentenceInclusion ≫ erase = 𝟙 sentences :=
  ForkPropositionalEmbedding.retraction
example : Mono embedding := inferInstance
example {j k : WalkingSpan} (f : j ⟶ k) : sentences.map f ≫ embedding.app k =
    embedding.app j ≫ firstOrder.sentenceObject.map f := ForkPropositionalEmbedding.naturality f

example (Y : Object) (a : labels ⟶ Y) (n : Y ⟶ Y) (i : Y ⨯ Y ⟶ Y)
    (m : sentences ⟶ Y) (ha : atom ≫ m = a) (hn : negation ≫ m = m ≫ n)
    (hi : implication ≫ m = prod.map m m ≫ i) :
    m = ForkPropositionalFolds.fold Y a n i :=
  ForkPropositionalFolds.unique Y a n i m ha hn hi

end CategoricalEssentialIncompleteness.V46.ForkErasureStatementChecks

namespace CategoricalEssentialIncompleteness.V46
#print axioms NullaryPropositionalErasure.erase
#print axioms NullaryPropositionalErasure.equality
#print axioms NullaryPropositionalErasure.atom_law
#print axioms NullaryPropositionalErasure.negation
#print axioms NullaryPropositionalErasure.implication
#print axioms NullaryPropositionalErasure.quantifier
#print axioms NullaryPropositionalErasure.unique
#print axioms NullaryPropositionalErasure.map
#print axioms ForkFirstOrderErasure.zeroArrow_total
#print axioms ForkFirstOrderErasure.erase
#print axioms ForkFirstOrderErasure.unique
#print axioms ForkFirstOrderErasure.naturality
#print axioms ForkPropositionalFolds.totalFold_unique
#print axioms ForkPropositionalFolds.fold
#print axioms ForkPropositionalFolds.fold_atom
#print axioms ForkPropositionalFolds.fold_negation
#print axioms ForkPropositionalFolds.fold_implication
#print axioms ForkPropositionalFolds.unique
#print axioms ForkPropositionalEmbedding.sentenceImplication
#print axioms ForkPropositionalEmbedding.embedding
#print axioms ForkPropositionalEmbedding.formula_implication
#print axioms ForkPropositionalEmbedding.retraction
#print axioms ForkPropositionalEmbedding.embedding_mono
#print axioms ForkPropositionalEmbedding.naturality
end CategoricalEssentialIncompleteness.V46
