import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionAll

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
example (q : RawPolynomial) (f g : ℕ → ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (allChildren f g q : ℕ → ℕ) := allChildren_primrec q f g hf hg
