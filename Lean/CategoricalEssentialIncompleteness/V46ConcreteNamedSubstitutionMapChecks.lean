import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionMap

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
example (q : RawPolynomial) (f g : M → M) (u : M) :
    shape q (mapChildren f g q u) = shape q u := shape_mapChildren q f g u
example (q : RawPolynomial) (f g : ℕ → ℕ) (hf : Primrec f) (hg : Primrec g) :
    Primrec (mapChildren f g q : ℕ → ℕ) := mapChildren_primrec q f g hf hg
