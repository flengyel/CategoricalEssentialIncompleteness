import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionFreeVariables

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
example (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ) :
    Nat.Primrec (freeVariables V σ π d : ℕ → ℕ) := freeVariables_natPrimrec V σ π d
example (V : Carrier) (σ π : ℕ → Carrier) (d : ℕ) (formula : Bool) (word : M)
    (h : (Postfix.carrier formula (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d)).val.Evalb ![word]) :
    (SyntacticLists.listCarrier V).val.Evalb ![freeVariables V σ π d word] :=
  freeVariables_carrier V σ π d formula word h
