import CategoricalEssentialIncompleteness.V46SyntacticFiniteDerivationsStandard

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticFiniteDerivations
namespace CategoricalEssentialIncompleteness.V46.SyntacticFiniteDerivations.StandardChecks
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] [ℕ↓[ℒₒᵣ] ⊧* T]
example {Fm : PredicateCategory T} {N : ℕ} (R : RulePresentation Fm N)
    (φ : SyntacticLists.Obj T ℕ Fm) :
    Derives T ℕ R φ ↔
      ∃ p : SyntacticLists.Obj T ℕ (SyntacticDerivation.derivationAlgebra T R).a.left,
        (SyntacticLists.F T ℕ).map (SyntacticDerivation.derivationAlgebra T R).a.hom p = φ :=
  standard_iff T R φ
end CategoricalEssentialIncompleteness.V46.SyntacticFiniteDerivations.StandardChecks
