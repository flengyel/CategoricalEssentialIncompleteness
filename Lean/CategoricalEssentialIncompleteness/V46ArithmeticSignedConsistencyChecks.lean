/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46ArithmeticSignedConsistency
public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPlain

/-! # Independent full consistency statements for constructed PA syntax -/
@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46
open SyntacticPredicates SyntacticDerivation ArithmeticSignedTheoryTruth
local notation "N" => (PrintedObjectCoding.Number : PredicateCategory 𝗣𝗔)
local notation "S" => SyntacticSyntax.plainCategoricalSyntax 𝗣𝗔 N
  (fun _ => ⊥_ (PredicateCategory 𝗣𝗔)) (fun _ => N) 0
local notation "Q" => derivationAlgebra 𝗣𝗔 (rules S)

example : 𝗣𝗔 ⊢
    let D := (Q).a.left
    let C := (chosenGraph 𝗣𝗔 (Q).a.hom).graph
    let G := (chosenGraph 𝗣𝗔 (S).negationConstructor).graph
    “∀ p q f n, !D.val p → !D.val q → !C.val p f → !C.val q n → !G.val f n → ⊥” :=
  consistency_PA S

example : imageSubobject (Q).a.hom ⊓
    (Subobject.pullback (S).negationConstructor).obj (imageSubobject (Q).a.hom) = ⊥ :=
  formula_consistent S

example : imageSubobject (pullback.snd (Q).a.hom (S).sentenceInclusion) ⊓
    (Subobject.pullback (S).sentenceNegation).obj
      (imageSubobject (pullback.snd (Q).a.hom (S).sentenceInclusion)) = ⊥ :=
  sentence_consistent S

#print axioms ArithmeticSignedTheoryTruth.consistencySentence
#print axioms ArithmeticSignedTheoryTruth.consistencySentence_eval
#print axioms ArithmeticSignedTheoryTruth.consistency_PA
#print axioms ArithmeticSignedTheoryTruth.formulaTheory
#print axioms ArithmeticSignedTheoryTruth.sentenceTheory
#print axioms ArithmeticSignedTheoryTruth.formula_consistent
#print axioms ArithmeticSignedTheoryTruth.sentenceTheory_eq_pullback
#print axioms ArithmeticSignedTheoryTruth.sentence_consistent
