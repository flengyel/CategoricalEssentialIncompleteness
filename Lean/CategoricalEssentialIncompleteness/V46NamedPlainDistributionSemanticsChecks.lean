import CategoricalEssentialIncompleteness.V46NamedPlainDistributionSemantics

universe w
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.NamedPlainDistributionSemanticsChecks
open SyntacticSyntax NamedPostfixEncoding NamedPlainSemantics
variable (σ π : ℕ → Carrier) (d : ℕ) {K : Type w}
variable (functions : ∀ n : Fin (d + 1), Symbols σ n.val → (Fin n.val → K) → K)
  (relations : ∀ n : Fin (d + 1), Symbols π n.val → (Fin n.val → K) → Prop)
example (r : Obj 𝗣𝗔 ℕ (plainCategoricalSyntax 𝗣𝗔 variableCarrier σ π d).distributionParameters) :
    Valid σ π d functions relations
      ((F 𝗣𝗔 ℕ).map (plainCategoricalSyntax 𝗣𝗔 variableCarrier σ π d).hilbertDistribution r) :=
  valid_hilbertDistribution σ π d functions relations r
end CategoricalEssentialIncompleteness.V46.NamedPlainDistributionSemanticsChecks
