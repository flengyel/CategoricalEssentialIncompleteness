import CategoricalEssentialIncompleteness.V46DerivationConclusionInduction

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.DerivationConclusionInductionChecks
open SyntacticDerivation SyntacticDerivation.StandardInduction
variable {Fm : PredicateCategory 𝗣𝗔} {bound : ℕ} (R : RulePresentation Fm bound)
example (i : Fin (bound + 1)) (k : Fin i.val) :
    typedChild 𝗣𝗔 R i k ≫ (derivationAlgebra 𝗣𝗔 R).a.hom = typedPremise 𝗣𝗔 R i k :=
  typedChild_conclusion 𝗣𝗔 R i k
example (P : Obj 𝗣𝗔 ℕ Fm → Prop)
    (step : ∀ (i : Fin (bound + 1))
      (r : Obj 𝗣𝗔 ℕ (R.ruleObject (derivationAlgebra 𝗣𝗔 R).a i)),
      (∀ k : Fin i.val, P ((F 𝗣𝗔 ℕ).map (typedPremise 𝗣𝗔 R i k) r)) →
        P ((F 𝗣𝗔 ℕ).map (R.ruleConclusion (derivationAlgebra 𝗣𝗔 R).a i) r)) :
    ∀ d : Obj 𝗣𝗔 ℕ (derivationAlgebra 𝗣𝗔 R).a.left,
      P ((F 𝗣𝗔 ℕ).map (derivationAlgebra 𝗣𝗔 R).a.hom d) :=
  conclusion_induction 𝗣𝗔 R P step
end CategoricalEssentialIncompleteness.V46.DerivationConclusionInductionChecks
