/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticDomainExtension
public import CategoricalEssentialIncompleteness.V46NamedArithmeticDiagonalBoundsPrinted
public import CategoricalEssentialIncompleteness.V46NamedArithmeticDiagonalLiteralTotal

/-! # The diagonal representation on the proper sentence object

The sentence theory is the range of the realized Γ-conclusion map. The two
inverse-image bounds use the canonical splitting-domain extension, and the code model
is any structure elementarily equivalent to ℕ.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.RestrictionCategory
open FailureOfComposition FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ArithmeticDiagonalRepresentation
open NamedArithmeticSignature

abbrev theta := NamedArithmeticDiagonalLiteralTotal.theta

theorem theta_total : isTotal theta.hom := theta.property

/-- The standard value is the named α-instance with the already compared expanded numeral,
with all generated binder names retained. -/
theorem theta_standard (n : ℕ) :
    ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ).map theta
      (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 ℕ n)).val.val =
        formulaCode (NamedArithmeticDiagonalBounds.instanceFormula
          ArithmeticDiagonalCodes.alpha.val n) :=
  (NamedArithmeticDiagonalLiteralTotal.canonical_value_at ℕ n).trans
    (NamedArithmeticDiagonalBounds.standard_instance_result ArithmeticDiagonalCodes.alpha.val n).1

section PA
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

/-- Interpret a total sentence morphism with the existing canonical
domain functor and the proved natural-number chart on its input. -/
def modelTheta (f : ArithmeticOmegaComparison.identityOmega 𝗣𝗔 ⟶
    NamedArithmeticLiteralTotal.literalSentence) :
    PartialFun.of M ⟶ PartialFun.of
      ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 M).obj
        NamedArithmeticLiteralTotal.literalSentence) :=
  fun n => Part.some ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 M).map f
    (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 M n))

theorem modelTheta_eq : modelTheta M theta =
    ArithmeticLiteralCoordinates.thetaMap M NamedArithmeticDiagonalBounds.namedAlpha
      NamedArithmeticDiagonalBounds.namedAlpha_freeVariables := rfl

/-- The inverse image through the sentence-valued morphism agrees with interpretation of
the source numerical inverse image. -/
theorem positive_comparison (Γ : Carrier) (φ : Formula)
    (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) :
    Idem.pull (ArithmeticLiteralCoordinates.thetaMap M φ hφ)
      ((ArithmeticDomainExtension.canonicalExtension M).mapIdem
        (ArithmeticDomainExtension.sentenceTheory Γ)) =
      (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem
        (Idem.pull (NamedArithmeticProofSearch.sourceTheta φ hφ)
          (predicateIdem 𝗣𝗔 (SyntacticGeneratedAxioms.literalTheoremCarrier 𝗣𝗔
            variableSymbols functionSymbols relationSymbols bound Γ))) := by
  exact (congrArg (Idem.pull (ArithmeticLiteralCoordinates.thetaMap M φ hφ))
      (ArithmeticDomainExtension.interpreted_theory M Γ)).trans
    ((ArithmeticLiteralCoordinates.theta_theory_pull M Γ φ hφ).trans
      (NamedArithmeticProofSearch.positive_source_pull_model M Γ φ hφ).symm)

theorem negative_comparison (Γ : Carrier) (φ : Formula)
    (hφ : ∀ y, y ∈ φ.freeVariables → y = 0) :
    Idem.pull (ArithmeticLiteralCoordinates.thetaMap M φ hφ)
      (Idem.pull ((ArithmeticDomainExtension.canonicalExtension M).toFunctor.map
        ArithmeticDomainExtension.sentenceNegation)
        ((ArithmeticDomainExtension.canonicalExtension M).mapIdem
          (ArithmeticDomainExtension.sentenceTheory Γ))) =
      (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem
        (Idem.pull (NamedArithmeticProofSearch.sourceTheta φ hφ)
          (predicateIdem 𝗣𝗔 (SyntacticGeneratedAxioms.literalRefutationCarrier 𝗣𝗔
            variableSymbols functionSymbols relationSymbols bound Γ))) := by
  have hν := congrArg₂ (fun f a => Idem.pull f a)
    (ArithmeticDomainExtension.interpreted_negation M)
    (ArithmeticDomainExtension.interpreted_theory M Γ)
  exact (congrArg (Idem.pull (ArithmeticLiteralCoordinates.thetaMap M φ hφ)) hν).trans
    ((ArithmeticLiteralCoordinates.theta_refutation_pull M Γ φ hφ).trans
      (NamedArithmeticProofSearch.negative_source_pull_model M Γ φ hφ).symm)

end PA

/-- Both bounds of Lemma 8.1 hold when Γ extends PA in the named calculus. Elementary
equivalence gives PA in the code model. -/
theorem bounds (Γ : Carrier) (hΓ : ArithmeticNamedAxiomComparison.ExtendsPA Γ)
    (M : Type) [ORingStructure M] [M ≡ₑ[ℒₒᵣ] ℕ] :
    letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := Tarski.Structure.ElementaryEquiv.modelsTheory' M ℕ 𝗣𝗔
    (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem ArithmeticDiagonalCodes.a0 ≤
      Idem.pull (modelTheta M theta)
        ((ArithmeticDomainExtension.canonicalExtension M).mapIdem
          (ArithmeticDomainExtension.sentenceTheory Γ)) ∧
    (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem ArithmeticDiagonalCodes.a1 ≤
      Idem.pull (modelTheta M theta)
        (Idem.pull ((ArithmeticDomainExtension.canonicalExtension M).toFunctor.map
          ArithmeticDomainExtension.sentenceNegation)
          ((ArithmeticDomainExtension.canonicalExtension M).mapIdem
            (ArithmeticDomainExtension.sentenceTheory Γ))) := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := Tarski.Structure.ElementaryEquiv.modelsTheory' M ℕ 𝗣𝗔
  have hp := (congrArg (fun f => Idem.pull f
      ((ArithmeticDomainExtension.canonicalExtension M).mapIdem
        (ArithmeticDomainExtension.sentenceTheory Γ))) (modelTheta_eq M)).trans
    (positive_comparison M Γ NamedArithmeticDiagonalBounds.namedAlpha
      NamedArithmeticDiagonalBounds.namedAlpha_freeVariables)
  have hn := (congrArg (fun f => Idem.pull f
      (Idem.pull ((ArithmeticDomainExtension.canonicalExtension M).toFunctor.map
        ArithmeticDomainExtension.sentenceNegation)
        ((ArithmeticDomainExtension.canonicalExtension M).mapIdem
          (ArithmeticDomainExtension.sentenceTheory Γ)))) (modelTheta_eq M)).trans
    (negative_comparison M Γ NamedArithmeticDiagonalBounds.namedAlpha
      NamedArithmeticDiagonalBounds.namedAlpha_freeVariables)
  exact ⟨hp.symm ▸ NamedArithmeticDiagonalBounds.model_positive M Γ hΓ,
    hn.symm ▸ NamedArithmeticDiagonalBounds.model_negative M Γ hΓ⟩

/-- One total sentence morphism gives the diagonal instance at every standard numeral and
satisfies both bounds of Lemma 8.1 for every Γ and code model in the statement. -/
theorem printed_representation :
    ∃ f : ArithmeticOmegaComparison.identityOmega 𝗣𝗔 ⟶
        NamedArithmeticLiteralTotal.literalSentence,
      isTotal f.hom ∧
      (∀ n : ℕ, ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ).map f
        (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 ℕ n)).val.val =
          formulaCode (NamedArithmeticDiagonalBounds.instanceFormula
            ArithmeticDiagonalCodes.alpha.val n)) ∧
      ∀ Γ : Carrier, ArithmeticNamedAxiomComparison.ExtendsPA Γ →
        ∀ (M : Type) [ORingStructure M] [M ≡ₑ[ℒₒᵣ] ℕ],
          letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := Tarski.Structure.ElementaryEquiv.modelsTheory' M ℕ 𝗣𝗔
          (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem ArithmeticDiagonalCodes.a0 ≤
            Idem.pull (modelTheta M f)
              ((ArithmeticDomainExtension.canonicalExtension M).mapIdem
                (ArithmeticDomainExtension.sentenceTheory Γ)) ∧
          (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem ArithmeticDiagonalCodes.a1 ≤
            Idem.pull (modelTheta M f)
              (Idem.pull ((ArithmeticDomainExtension.canonicalExtension M).toFunctor.map
                ArithmeticDomainExtension.sentenceNegation)
                ((ArithmeticDomainExtension.canonicalExtension M).mapIdem
                  (ArithmeticDomainExtension.sentenceTheory Γ))) :=
  ⟨theta,theta_total,theta_standard,fun Γ hΓ M _ _ => bounds Γ hΓ M⟩

end CategoricalEssentialIncompleteness.V46.ArithmeticDiagonalRepresentation
