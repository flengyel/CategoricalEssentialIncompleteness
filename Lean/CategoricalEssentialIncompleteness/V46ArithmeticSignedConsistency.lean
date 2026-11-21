/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticSignedConsistencyPA
public import CategoricalEssentialIncompleteness.V46PredicateImageConsistency
public import CategoricalEssentialIncompleteness.V46ConsistentFirstOrderTheories

/-! # Consistency of the formula and sentence subobjects of the diagonal signed calculus -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ArithmeticSignedTheoryTruth
open SyntacticDerivation
local notation "N" => (PrintedObjectCoding.Number : PredicateCategory 𝗣𝗔)
variable {V : PredicateCategory 𝗣𝗔}
variable (S : CategoricalSyntax V (fun _ => ⊥_ (PredicateCategory 𝗣𝗔)) (fun _ => N) 0)
local notation "Q" => derivationAlgebra 𝗣𝗔 (rules S)

/-- The image of the conclusion morphism from the object of derivations to the
formula object. -/
def formulaTheory : Subobject S.algebra.a.2 := imageSubobject (Q).a.hom

/-- The image of the conclusion morphism after pullback along the inclusion of
sentences into formulas. -/
def sentenceTheory : Subobject S.sentenceObject :=
  imageSubobject (pullback.snd (Q).a.hom S.sentenceInclusion)

theorem formula_consistent :
    formulaTheory S ⊓ (Subobject.pullback S.negationConstructor).obj (formulaTheory S) = ⊥ :=
  PredicateImageConsistency.image_consistent 𝗣𝗔 (Q).a.hom S.negationConstructor
    (fun M _ _ p q => no_contradictory_derivations S M p q)

theorem sentenceTheory_eq_pullback :
    sentenceTheory S = (Subobject.pullback S.sentenceInclusion).obj (formulaTheory S) :=
  sentenceImage_subobject (Q).a.hom S.sentenceInclusion

/-- The subobject of derivable sentences is disjoint from its inverse image under
sentence negation. -/
theorem sentence_consistent :
    sentenceTheory S ⊓ (Subobject.pullback S.sentenceNegation).obj (sentenceTheory S) = ⊥ := by
  have hn : (Subobject.pullback S.sentenceNegation).obj
      ((Subobject.pullback S.sentenceInclusion).obj (formulaTheory S)) =
      (Subobject.pullback S.sentenceInclusion).obj
        ((Subobject.pullback S.negationConstructor).obj (formulaTheory S)) := by
    rw [← Subobject.pullback_comp, S.sentenceNegation_inclusion, Subobject.pullback_comp]
  simp only [sentenceTheory_eq_pullback]
  rw [hn, ← Subobject.inf_pullback, formula_consistent, PresentationLemmas.pullback_bot]

end CategoricalEssentialIncompleteness.V46.ArithmeticSignedTheoryTruth
