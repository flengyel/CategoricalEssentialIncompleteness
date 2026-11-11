/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticUniformSentence


/-! # Statement checks in `V46ArithmeticUniformSentenceChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.RestrictionCategory
open FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.ArithmeticUniformSentenceChecks
open ArithmeticUniformSearch NamedArithmeticSignature
example (g : omegaObject 𝗣𝗔 ⟶ omegaObject 𝗣𝗔) (hg : isTotal g) :
    (totalEndomorphism g hg).hom.hom = g := totalEndomorphism_underlying g hg
example (g : omegaObject 𝗣𝗔 ⟶ omegaObject 𝗣𝗔) (hg : isTotal g)
    (φ : Formula) (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) :
    SourceComposite (D := TotalSplit 𝗣𝗔) (totalEndomorphism g hg)
      (NamedArithmeticLiteralTotal.theta φ hφ) := sentenceData g hg φ hφ
example (C C' : 𝚺₁.Semisentence 2) (φ : Formula)
    (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) :
    ArithmeticOmegaComparison.identityOmega 𝗣𝗔 ⟶ NamedArithmeticLiteralTotal.literalSentence :=
  sentenceMorphism C C' φ hφ
example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (C C' : 𝚺₁.Semisentence 2) (φ : Formula)
    (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) (e : M) :
    ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 M).map (sentenceMorphism C C' φ hφ)
      (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 M e)).val.val =
        NamedArithmeticFixedSubstitution.value φ (output M C C' e) :=
  sentenceMorphism_value M C C' φ hφ e
end CategoricalEssentialIncompleteness.V46.ArithmeticUniformSentenceChecks
