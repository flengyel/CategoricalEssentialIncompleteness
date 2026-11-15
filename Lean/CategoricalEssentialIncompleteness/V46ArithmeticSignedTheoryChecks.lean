/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46ArithmeticSignedTheory

/-! # Independent checks of every printed clause of Lemma 8.9

The axiom join, proof construction, actual split generators, free syntax
and all closed extensions are stated explicitly here.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46
open LocalConnectedness SyntacticPredicates ArithmeticSignedAtoms
local notation "F₀" => ArithmeticSignedTheory.presentation
local notation "N" => (PrintedObjectCoding.Number : PredicateCategory 𝗣𝗔)
local notation "S" => NullaryPresentations.syntaxData (F₀) N
local notation "G" => SyntacticPredicates.realization 𝗣𝗔

example : (interpretedObject 𝗣𝗔 N).obj =
    (splittingInclusion (C := CodedProgramCategory 𝗣𝗔)).obj (omegaObject 𝗣𝗔) :=
  ArithmeticSignedSplitGenerators.number_object

example : ((G).map (numberInclusion ArithmeticDiagonalCodes.alpha)).hom.hom =
    ArithmeticDiagonalCodes.a0.hom := ArithmeticSignedSplitGenerators.positive_underlying

example : ((G).map (numberInclusion ArithmeticDiagonalCodes.beta)).hom.hom =
    ArithmeticDiagonalCodes.a1.hom := ArithmeticSignedSplitGenerators.negative_underlying

example : ArithmeticSignedTotal.axioms (F₀) =
    imageSubobject ((G).map (numberInclusion ArithmeticDiagonalCodes.alpha) ≫
      (G).map (NullaryInterpretation.atomSentence (S))) ⊔
    imageSubobject ((G).map (numberInclusion ArithmeticDiagonalCodes.beta) ≫
      (G).map (NullaryInterpretation.atomSentence (S)) ≫ (G).map (S).sentenceNegation) :=
  ArithmeticSignedTotal.axioms_image (F₀)

example (A : Subobject ((G).obj (S).sentenceObject)) :
    IsInitial (SyntacticDerivation.totalDerivationAlgebra 𝗣𝗔
      (firstOrderRules ((G).map (S).logicalAxioms) ((G).map (S).sentenceInclusion) A.arrow
        (FirstOrderRuleTransport.mappedAll (G) (S).quantifierConstructor)
        (FirstOrderRuleTransport.mappedImp (G) (S).implicationConstructor))) :=
  ArithmeticSignedTotal.initial (F₀) A

example : IsInitial (ArithmeticSignedTotal.syntaxAlgebra (F₀)) :=
  ArithmeticSignedTotal.syntaxInitial (F₀)

example (P : TotalSplit 𝗣𝗔) : IsInitial
    (SyntaxPolynomial.algebraWithParameters
      (SyntaxPolynomial.termExpression ((G).obj N)
        (fun _ => (G).obj (⊥_ (PredicateCategory 𝗣𝗔))) 0)
      (SyntaxPolynomial.formulaExpression ((G).obj N) (fun _ => (G).obj N) 0)
      (ArithmeticSignedTotal.syntaxAlgebra (F₀)) P) :=
  ArithmeticSignedTotal.syntaxStable (F₀) P

example : (ArithmeticSignedTotal.syntaxAlgebra (F₀)).a =
    ((G).obj (S).algebra.a.1, (G).obj (S).algebra.a.2) :=
  ArithmeticSignedTotal.syntax_carrier (F₀)

/-- The complete printed conclusion, with the actual initial proof
family, literal signed image join and both consistency equations. -/
example (_hPA : Entailment.Consistent 𝗣𝗔) :
    let ν := (G).map (S).sentenceNegation
    let θ := (G).map (NullaryInterpretation.atomSentence (S))
    let Γ := imageSubobject ((G).map (numberInclusion ArithmeticDiagonalCodes.alpha) ≫ θ) ⊔
      imageSubobject ((G).map (numberInclusion ArithmeticDiagonalCodes.beta) ≫ θ ≫ ν)
    let T := FirstOrderReflection.generated (ArithmeticSignedTotal.proofs (F₀)) Γ
    Inseparable (SplitObject.includedIdem ArithmeticDiagonalCodes.a0)
      (SplitObject.includedIdem ArithmeticDiagonalCodes.a1) ∧
    T ⊓ (Subobject.pullback ν).obj T = ⊥ ∧
    ∀ U : FirstOrderReflection.Theory (ArithmeticSignedTotal.proofs (F₀)), T ≤ U.val →
      U.val ⊓ (Subobject.pullback ν).obj U.val = ⊥ →
      U.val ⊔ (Subobject.pullback ν).obj U.val ≠ ⊤ := by
  dsimp only
  have h := ArithmeticSignedTheory.printed_statement _hPA
  simp only [ArithmeticSignedTotal.theory, ArithmeticSignedTotal.axioms_image,
    ArithmeticSignedTotal.atom, ArithmeticSignedTotal.negation] at h
  exact h

example {A : TotalSplit 𝗣𝗔} (a : A ⟶ (G).obj (S).sentenceObject) :
    ((FirstOrderReflection.presentationGeneration (ArithmeticSignedTotal.proofs (F₀))
      (ArithmeticSignedTotal.initial (F₀))).obj (Over.mk a)).val =
      FirstOrderReflection.generated (ArithmeticSignedTotal.proofs (F₀)) (imageSubobject a) :=
  ArithmeticSignedTheory.presentation_generation a

#print axioms ArithmeticSignedTotal.axioms_comparison
#print axioms ArithmeticSignedTotal.axioms_image
#print axioms ArithmeticSignedTotal.theory_le_image
#print axioms ArithmeticSignedTotal.consistent
#print axioms ArithmeticSignedTotal.atomic_bounds
#print axioms ArithmeticSignedTotal.inseparable
#print axioms ArithmeticSignedTotal.every_consistent_extension_incomplete
#print axioms ArithmeticSignedTotal.essentially_incomplete
#print axioms ArithmeticSignedSplitGenerators.number_idem
#print axioms ArithmeticSignedSplitGenerators.number_object
#print axioms ArithmeticSignedSplitGenerators.alpha_object
#print axioms ArithmeticSignedSplitGenerators.beta_object
#print axioms ArithmeticSignedSplitGenerators.positive_underlying
#print axioms ArithmeticSignedSplitGenerators.negative_underlying
#print axioms ArithmeticSignedTotal.syntaxInitial
#print axioms ArithmeticSignedTotal.syntaxStable
#print axioms ArithmeticSignedTotal.syntax_carrier
#print axioms ArithmeticSignedTotal.noFunctions
#print axioms ArithmeticSignedTheory.printed_statement
#print axioms ArithmeticSignedTheory.presentation_generation

#print axioms ForwardSyntaxTransport.mapped_fold
