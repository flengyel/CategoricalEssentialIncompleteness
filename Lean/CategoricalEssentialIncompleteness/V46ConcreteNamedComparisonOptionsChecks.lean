import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonOptions

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.OptionsChecks
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (C : PredicateCategory T)
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

example : RawOption T C ≅ OptionSyntax.obj C := optionIso T C
example (x : Obj T M C) :
    optionCode T M C ((F T M).map (coprod.inr : C ⟶ OptionSyntax.obj C) x) =
      Arithmetic.pair x.val 1 := optionCode_inr T M C x
example (x : Obj T M (OptionSyntax.obj C)) :
    π₂ (optionCode T M C x) = 1 ↔ ∃ y : Obj T M C,
      (F T M).map (coprod.inr : C ⟶ OptionSyntax.obj C) y = x :=
  optionCode_tag_success T M C x
end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.OptionsChecks
