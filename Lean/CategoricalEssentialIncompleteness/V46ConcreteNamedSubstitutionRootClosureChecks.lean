import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionRootClosure

/-! Explicit PA-model and standard primitive-recursion statement checks. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding
open CategoricalEssentialIncompleteness.V46.ConcreteNamedSubstitution
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
example (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ) (param u : M)
    (h : (rawCarrier (termPayloadCarrier V σ π d) (formulaPayloadCarrier V σ π d)
      (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![u]) :
    (formulaPayloadCarrier V σ π d).val.Evalb ![formulaRoot V π d param u] :=
  formulaRoot_carrier V σ π d param u h
