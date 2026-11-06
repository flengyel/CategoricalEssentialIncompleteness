import CategoricalEssentialIncompleteness.V46SyntacticGeneratedRefutations

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticGeneratedAxioms
namespace CategoricalEssentialIncompleteness.V46.SyntacticGeneratedAxioms.RefutationChecks
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ) (Γ : Carrier)
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
example (word : M) :
    (refutationCarrier T V σ π d Γ).val.Evalb ![word] ↔
      (literalRefutationCarrier T V σ π d Γ).val.Evalb ![word] :=
  refutationCarrier_literal T V σ π d M Γ word
example : T ⊢ refutationLiteralSentence T V σ π d Γ := refutation_literal_theory T V σ π d Γ
end CategoricalEssentialIncompleteness.V46.SyntacticGeneratedAxioms.RefutationChecks
