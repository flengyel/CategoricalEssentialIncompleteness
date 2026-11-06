import CategoricalEssentialIncompleteness.V46ArithmeticInternalComparison

/-! # Exact Theorem 7.3 statements for the constructed Gamma -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.RestrictionCategory Filter
open FailureOfComposition.TypedProgramCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.LocalConnectedness.PartialFunctions
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.ArithmeticInternalComparison.Checks
open NamedArithmeticSignature
variable (A : Carrier) (hPA : ArithmeticNamedAxiomComparison.ExtendsPA A)
variable (hc : Entailment.Consistent (ArithmeticNamedProofConnectives.system A))
include hPA hc

example :
    ∃ g : omegaObject 𝗣𝗔 ⟶ omegaObject 𝗣𝗔, isTotal g ∧
      Idem.pull ((SyntacticModel.modelFunctor 𝗣𝗔 ℕ).map g ≫
        ArithmeticLiteralCoordinates.thetaMap ℕ ArithmeticComparisonTarget.diagonalFormula
          ArithmeticComparisonTarget.diagonalFormula_freeVariables)
        (ArithmeticLiteralCoordinates.theory ℕ A) = ⊥ ∧
      Idem.pull ((SyntacticModel.modelFunctor 𝗣𝗔 ℕ).map g ≫
        ArithmeticLiteralCoordinates.thetaMap ℕ ArithmeticComparisonTarget.diagonalFormula
          ArithmeticComparisonTarget.diagonalFormula_freeVariables)
        (Idem.pull (ArithmeticLiteralCoordinates.negationMap ℕ)
          (ArithmeticLiteralCoordinates.theory ℕ A)) = ⊥ ∧
      ArithmeticLiteralCoordinates.theory ℕ A ⊔
        Idem.pull (ArithmeticLiteralCoordinates.negationMap ℕ)
          (ArithmeticLiteralCoordinates.theory ℕ A) ≠ ⊤ := standard_comparison A hPA hc

example :
    ArithmeticDomainExtension.sentenceTheory A ⊔
      Idem.pull ArithmeticDomainExtension.sentenceNegation
        (ArithmeticDomainExtension.sentenceTheory A) ≠ ⊤ := source_incomplete A hPA hc

example :
    ArithmeticLiteralCoordinates.theory ℕ A ⊔
      Idem.pull (ArithmeticLiteralCoordinates.negationMap ℕ)
        (ArithmeticLiteralCoordinates.theory ℕ A) ≠ ⊤ := standard_incomplete A hPA hc

example {I : Type} (U : Ultrafilter I) :
    ArithmeticLiteralCoordinates.theory (ArithmeticUltrapower.Model U) A ⊔
      Idem.pull (ArithmeticLiteralCoordinates.negationMap (ArithmeticUltrapower.Model U))
        (ArithmeticLiteralCoordinates.theory (ArithmeticUltrapower.Model U) A) ≠ ⊤ :=
  ultrapower_incomplete A hPA hc U

example :
    (ArithmeticDomainExtension.canonicalExtension ℕ).mapIdem
        (ArithmeticDomainExtension.sentenceTheory A) ⊔
      Idem.pull ((ArithmeticDomainExtension.canonicalExtension ℕ).toFunctor.map
        ArithmeticDomainExtension.sentenceNegation)
        ((ArithmeticDomainExtension.canonicalExtension ℕ).mapIdem
          (ArithmeticDomainExtension.sentenceTheory A)) ≠ ⊤ := interpreted_standard_incomplete A hPA hc

example {I : Type} (U : Ultrafilter I) :
    (ArithmeticDomainExtension.canonicalExtension (ArithmeticUltrapower.Model U)).mapIdem
        (ArithmeticDomainExtension.sentenceTheory A) ⊔
      Idem.pull ((ArithmeticDomainExtension.canonicalExtension (ArithmeticUltrapower.Model U)).toFunctor.map
        ArithmeticDomainExtension.sentenceNegation)
        ((ArithmeticDomainExtension.canonicalExtension (ArithmeticUltrapower.Model U)).mapIdem
          (ArithmeticDomainExtension.sentenceTheory A)) ≠ ⊤ := interpreted_ultrapower_incomplete A hPA hc U

example :
    ∃ g : omegaObject 𝗣𝗔 ⟶ omegaObject 𝗣𝗔, isTotal g ∧
      ∃ gamma : ℕ → ℕ,
        (∀ n : ℕ, gamma n ∈ (SyntacticModel.modelFunctor 𝗣𝗔 ℕ).map g n) ∧
        ∀ n : ℕ,
          let φ := NamedArithmeticDiagonalBounds.instanceFormula ArithmeticDiagonalCodes.alpha.val (gamma n)
          ArithmeticComparisonTarget.diagonalFormula.substitute 0 (numeral (gamma n)) = some φ ∧
          φ.freeVariables = [] ∧
          ¬ SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A φ ∧
          ¬ SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A (.neg φ) :=
  total_undecidable_family A hPA hc

example :
    (ArithmeticDomainExtension.sentenceTheory A ⊔
      Idem.pull ArithmeticDomainExtension.sentenceNegation
        (ArithmeticDomainExtension.sentenceTheory A) ≠ ⊤) ∧
    ((ArithmeticDomainExtension.canonicalExtension ℕ).mapIdem
        (ArithmeticDomainExtension.sentenceTheory A) ⊔
      Idem.pull ((ArithmeticDomainExtension.canonicalExtension ℕ).toFunctor.map
        ArithmeticDomainExtension.sentenceNegation)
        ((ArithmeticDomainExtension.canonicalExtension ℕ).mapIdem
          (ArithmeticDomainExtension.sentenceTheory A)) ≠ ⊤) ∧
    (∀ (I : Type) (U : Ultrafilter I),
      (ArithmeticDomainExtension.canonicalExtension (ArithmeticUltrapower.Model U)).mapIdem
          (ArithmeticDomainExtension.sentenceTheory A) ⊔
        Idem.pull ((ArithmeticDomainExtension.canonicalExtension (ArithmeticUltrapower.Model U)).toFunctor.map
          ArithmeticDomainExtension.sentenceNegation)
          ((ArithmeticDomainExtension.canonicalExtension (ArithmeticUltrapower.Model U)).mapIdem
            (ArithmeticDomainExtension.sentenceTheory A)) ≠ ⊤) ∧
    (∃ g : omegaObject 𝗣𝗔 ⟶ omegaObject 𝗣𝗔, isTotal g ∧
      ∃ gamma : ℕ → ℕ,
        (∀ n : ℕ, gamma n ∈ (SyntacticModel.modelFunctor 𝗣𝗔 ℕ).map g n) ∧
        ∀ n : ℕ,
          let φ := NamedArithmeticDiagonalBounds.instanceFormula ArithmeticDiagonalCodes.alpha.val (gamma n)
          ArithmeticComparisonTarget.diagonalFormula.substitute 0 (numeral (gamma n)) = some φ ∧
          φ.freeVariables = [] ∧
          ¬ SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A φ ∧
          ¬ SyntacticNamedHilbert.Derives functionSymbols relationSymbols bound A (.neg φ)) :=
  internal_comparison A hPA hc

end CategoricalEssentialIncompleteness.V46.ArithmeticInternalComparison.Checks
