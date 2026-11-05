import CategoricalEssentialIncompleteness.V46ConcreteNamedSubstitutionGather

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
example (q : RawPolynomial) (o u : M) :
    (gatherGraph q).val.Evalb ![o,u] ↔ o = gather q u := gatherGraph_eval q o u
example (q : RawPolynomial) : Primrec (gather q : ℕ → ℕ) := gather_primrec q
