import CategoricalEssentialIncompleteness.V46SyntacticSyntaxSize

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.SizeChecks
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
example (formula : Bool) (q : RawPolynomial) (u : M) :
    (childSizeGraph q).val.Evalb ![len (constructor formula q u), u] :=
  children_smaller formula q u
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.SizeChecks
