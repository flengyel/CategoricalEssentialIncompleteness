import CategoricalEssentialIncompleteness.V46ArithmeticUniformSentence
import CategoricalEssentialIncompleteness.V46NamedArithmeticProofSearchNegation
import CategoricalEssentialIncompleteness.V46NamedArithmeticDiagonalBoundsStandard

/-! # Joint substituted provability predicates

These use the actual named numeral-substitution and primitive-recursive
negation graphs. Instantiating P with the constructed family provability
predicate requires its proved numeral-fiber comparison.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ArithmeticUniformSearch
open NamedArithmeticSignature

/-- The numerical matrix C(e,x)=P(e,Θ(x)). The substitution graph has
its existing output/input coordinate order. -/
def positive (P : Predicate₂) (φ : Formula) : Predicate₂ :=
  let H := NamedArithmeticFixedSubstitution.graph φ
  .mkSigma “e x. ∃ word, !H.val word x ∧ !P.val e word”

/-- The numerical matrix C'(e,x)=P(e,Neg(Θ(x))) uses the proved total
primitive-recursive extension of the literal negation constructor. -/
def negative (P : Predicate₂) (φ : Formula) : Predicate₂ :=
  let H := NamedArithmeticFixedSubstitution.graph φ
  let Neg := NamedArithmeticProofSearch.negationWordGraph
  .mkSigma “e x. ∃ word negative, !H.val word x ∧ !Neg.val negative word ∧ !P.val e negative”

section Models
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

@[simp] theorem positive_eval (P : Predicate₂) (φ : Formula) (e x : M) :
    (positive P φ).val.Evalb ![e,x] ↔
      P.val.Evalb ![e,NamedArithmeticFixedSubstitution.value φ x] := by
  simp [positive]

@[simp] theorem negative_eval (P : Predicate₂) (φ : Formula) (e x : M) :
    (negative P φ).val.Evalb ![e,x] ↔
      P.val.Evalb ![e,NamedArithmeticProofSearch.negationWord M
        (NamedArithmeticFixedSubstitution.value φ x)] := by
  simp [negative]

end Models

/-- The printed sentence morphism for one joint provability matrix P.
Its definition contains no fiber consistency or model-soundness proof. -/
def proofSentenceMorphism (P : Predicate₂) :
    ArithmeticOmegaComparison.identityOmega 𝗣𝗔 ⟶ NamedArithmeticLiteralTotal.literalSentence :=
  sentenceMorphism (positive P NamedArithmeticDiagonalBounds.namedAlpha)
    (negative P NamedArithmeticDiagonalBounds.namedAlpha)
    NamedArithmeticDiagonalBounds.namedAlpha NamedArithmeticDiagonalBounds.namedAlpha_freeVariables

theorem proofSentenceMorphism_value (P : Predicate₂) (e : ℕ) :
    ((PredicateInterpretation.canonicalDomainFunctor 𝗣𝗔 ℕ).map (proofSentenceMorphism P)
      (NamedArithmeticLiteralTotal.omegaPoint 𝗣𝗔 ℕ e)).val.val =
        NamedArithmeticFixedSubstitution.value NamedArithmeticDiagonalBounds.namedAlpha
          (output ℕ (positive P NamedArithmeticDiagonalBounds.namedAlpha)
            (negative P NamedArithmeticDiagonalBounds.namedAlpha) e) :=
  sentenceMorphism_value ℕ _ _ _ NamedArithmeticDiagonalBounds.namedAlpha_freeVariables e

end CategoricalEssentialIncompleteness.V46.ArithmeticUniformSearch
