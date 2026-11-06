import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonPlainFreeFor

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.PlainFreeForChecks
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (V : PredicateCategory T) (σ π : ℕ → PredicateCategory T) (d : ℕ)
local notation "S" => plainCategoricalSyntax T V σ π d
local notation "P" => CategoricalSyntax.substitutionParameters (plainCategoricalSyntax T V σ π d)
local notation "X" => (plainSyntaxCarrier V σ π d false : PredicateCategory T)
local notation "Y" => (plainSyntaxCarrier V σ π d true : PredicateCategory T)

example : IsPullback (S).admissibleInclusion (terminal.from (S).admissibleSubstitution)
    (plainFreeForClassifier T V σ π d) (Two.point (C := PredicateCategory T) true) :=
  plainFreeForClassifier_isPullback T V σ π d

example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q : Obj T M (Y ⨯ P)) :
    (F T M).map (plainFreeForClassifier T V σ π d) q =
      (F T M).map (Two.constant (C := PredicateCategory T) (Y ⨯ P) true) q ↔
      ConcreteNamedSubstitution.substitutionFreeFor V σ π d
        ((F T M).map (prod.fst : P ⟶ V) ((F T M).map prod.snd q)).val
        ((F T M).map (prod.snd : P ⟶ X) ((F T M).map prod.snd q)).val
        ((F T M).map prod.fst q).val = 1 :=
  plainFreeForClassifier_model_iff T V σ π d M q
end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison.PlainFreeForChecks
