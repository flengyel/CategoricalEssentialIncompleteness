/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ArithmeticDiagonalRepresentation

/-! # Full proper-sentence diagonal representation statements -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.RestrictionCategory
open FailureOfComposition FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.NamedArithmeticSignature
open CategoricalEssentialIncompleteness.V46.ArithmeticNamedAxiomComparison

namespace CategoricalEssentialIncompleteness.V46.ArithmeticDiagonalRepresentationChecks

example (Γ : Carrier)
    (hΓ : ∀ ψ : Formula,
      (ψ.freeVariables = [] ∧ ∃ φ, PASeed φ ∧ UniversalClosure φ ψ) →
      SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound Γ ψ)
    (M : Type) [ORingStructure M] [M ≡ₑ[ℒₒᵣ] ℕ] :
    letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := Tarski.Structure.ElementaryEquiv.modelsTheory' M ℕ 𝗣𝗔
    (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem ArithmeticDiagonalCodes.a0 ≤
      Idem.pull (fun n => Part.some
        ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 M).map
          NamedArithmeticDiagonalLiteralTotal.theta
          (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 M n)))
        ((ArithmeticDomainExtension.canonicalExtension M).mapIdem
          (Ranges.range ((realization 𝗣𝗔).map (ArithmeticLiteralModel.conclusion Γ)).hom)) ∧
    (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem ArithmeticDiagonalCodes.a1 ≤
      Idem.pull (fun n => Part.some
        ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 M).map
          NamedArithmeticDiagonalLiteralTotal.theta
          (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 M n)))
        (Idem.pull ((ArithmeticDomainExtension.canonicalExtension M).toFunctor.map
          ((realization 𝗣𝗔).map ArithmeticLiteralModel.negation).hom)
          ((ArithmeticDomainExtension.canonicalExtension M).mapIdem
            (Ranges.range ((realization 𝗣𝗔).map (ArithmeticLiteralModel.conclusion Γ)).hom))) :=
  ArithmeticDiagonalRepresentation.bounds Γ hΓ M

example :
    ∃ f : ArithmeticOmegaComparison.identityOmega 𝗣𝗔 ⟶
        NamedArithmeticLiteralTotal.literalSentence,
      isTotal f.hom ∧
      (∀ n : ℕ, ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ).map f
        (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 ℕ n)).val.val =
          formulaCode (ArithmeticNamedTranslation.translateFormula 1 ![]
            (ArithmeticDiagonalCodes.alpha.val/[
              ArithmeticNamedProofNumerals.expandedNumeral n] : ArithmeticSentence))) ∧
      ∀ Γ : Carrier,
        (∀ ψ : Formula,
          (ψ.freeVariables = [] ∧ ∃ φ, PASeed φ ∧ UniversalClosure φ ψ) →
          SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound Γ ψ) →
        ∀ (M : Type) [ORingStructure M] [M ≡ₑ[ℒₒᵣ] ℕ],
          letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := Tarski.Structure.ElementaryEquiv.modelsTheory' M ℕ 𝗣𝗔
          (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem ArithmeticDiagonalCodes.a0 ≤
            Idem.pull (ArithmeticDiagonalRepresentation.modelTheta M f)
              ((ArithmeticDomainExtension.canonicalExtension M).mapIdem
                (Ranges.range ((realization 𝗣𝗔).map (ArithmeticLiteralModel.conclusion Γ)).hom)) ∧
          (SyntacticModel.modelRangeFunctor 𝗣𝗔 M).mapIdem ArithmeticDiagonalCodes.a1 ≤
            Idem.pull (ArithmeticDiagonalRepresentation.modelTheta M f)
              (Idem.pull ((ArithmeticDomainExtension.canonicalExtension M).toFunctor.map
                ((realization 𝗣𝗔).map ArithmeticLiteralModel.negation).hom)
                ((ArithmeticDomainExtension.canonicalExtension M).mapIdem
                  (Ranges.range ((realization 𝗣𝗔).map (ArithmeticLiteralModel.conclusion Γ)).hom))) :=
  ArithmeticDiagonalRepresentation.printed_representation

end CategoricalEssentialIncompleteness.V46.ArithmeticDiagonalRepresentationChecks
