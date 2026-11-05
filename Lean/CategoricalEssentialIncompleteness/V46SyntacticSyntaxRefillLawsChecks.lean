import CategoricalEssentialIncompleteness.V46SyntacticSyntaxRefillLaws

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.RefillLawsChecks
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

example (q : RawPolynomial) (s stack u rest tail : M)
    (h : refill q s stack = adjoin u rest) :
    refill q s (Words.append stack tail) = adjoin u (Words.append rest tail) :=
  refill_frame q s stack u rest tail h

example (q : RawPolynomial) (s stack u rest : M)
    (h : refill q s stack = adjoin u rest) :
    shape q u = s ∧ childStack q u rest = stack := refill_sound q s stack u rest h

example (X Y : Carrier) (q : RawPolynomial) (s stack u rest : M)
    (hs : (rawCarrier zeroCarrier zeroCarrier q).val.Evalb ![s])
    (hst : (stackCarrier X Y).val.Evalb ![stack])
    (h : refill q s stack = adjoin u rest) :
    (rawCarrier X Y q).val.Evalb ![u] ∧ (stackCarrier X Y).val.Evalb ![rest] :=
  refill_typed X Y q s stack u rest hs hst h
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.RefillLawsChecks
