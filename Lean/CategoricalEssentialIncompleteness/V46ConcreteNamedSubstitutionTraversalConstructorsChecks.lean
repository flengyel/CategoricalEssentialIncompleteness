import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionTraversalConstructors

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
example (a b : RawPolynomial) (F G : 𝚺₁.Semisentence 3) (f g : M → M → M)
    [𝚺₁-Function₂ f via F] [𝚺₁-Function₂ g via G] (param : M) (formula : Bool) (word : M)
    (h : (Postfix.carrier formula a b).val.Evalb ![word]) :
    Traversal.Good a b F G f g param formula word :=
  Traversal.accepted_good a b F G f g param formula word h
