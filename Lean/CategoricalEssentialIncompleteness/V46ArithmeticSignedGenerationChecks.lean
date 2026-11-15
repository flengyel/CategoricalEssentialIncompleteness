/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46ArithmeticSignedGeneration
public import CategoricalEssentialIncompleteness.V46SyntacticNullaryPresentations

/-! # Independent checks of regular-image generation and signed consistency -/
@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46
open SyntacticPredicates SyntacticDerivation ArithmeticSignedAtoms ArithmeticSignedTheoryTruth

variable {V : PredicateCategory 𝗣𝗔}
local notation "N" => (PrintedObjectCoding.Number : PredicateCategory 𝗣𝗔)

example (S : CategoricalSyntax V (fun _ => ⊥_ (PredicateCategory 𝗣𝗔)) (fun _ => N) 0)
    {A : PredicateCategory 𝗣𝗔} (a : A ⟶ S.sentenceObject) :
    imageSubobject (pullback.snd (derivationAlgebra 𝗣𝗔 (S.logicalRules a)).a.hom S.sentenceInclusion) =
      FirstOrderReflection.generated (proofFamily S) (imageSubobject a) :=
  presentation_image_comparison S a

example (F : NullaryPresentations V) :
    (SignedFirstOrder.theory F positiveSubobject negativeSubobject).val ⊓
      (Subobject.pullback (F.syntaxData N).sentenceNegation).obj
        (SignedFirstOrder.theory F positiveSubobject negativeSubobject).val = ⊥ :=
  signed_theory_consistent F

/-- Both syntax and the subobject-indexed initial proof family are constructed. -/
example :
    let F := nullaryPresentations 𝗣𝗔 N
    (SignedFirstOrder.theory F positiveSubobject negativeSubobject).val ⊓
      (Subobject.pullback (F.syntaxData N).sentenceNegation).obj
        (SignedFirstOrder.theory F positiveSubobject negativeSubobject).val = ⊥ :=
  signed_theory_consistent (nullaryPresentations 𝗣𝗔 N)

#print axioms ArithmeticSignedAtoms.numberInclusion_mono
#print axioms ArithmeticSignedAtoms.positiveSubobject
#print axioms ArithmeticSignedAtoms.negativeSubobject
#print axioms ArithmeticSignedTheoryTruth.proofFamily
#print axioms ArithmeticSignedTheoryTruth.proofFamily_initial
#print axioms ArithmeticSignedTheoryTruth.presentation_image_comparison
#print axioms ArithmeticSignedTheoryTruth.generated_eq_canonical
#print axioms ArithmeticSignedTheoryTruth.signed_axiom_image
#print axioms ArithmeticSignedTheoryTruth.signed_theory_eq
#print axioms ArithmeticSignedTheoryTruth.signed_theory_consistent
#print axioms SyntacticDerivation.nullaryPresentations
