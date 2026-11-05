import CategoricalEssentialIncompleteness.V46SyntacticSyntaxRefill

/-! Typed stack consumption is an actual PA-total graph, not a parsing interface assumption. -/
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open Coding
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
example (p : RawPolynomial) (o shape stack : M) :
    (refillGraph p).val.Evalb ![o, shape, stack] ↔ o = refill p shape stack :=
  refillGraph_eval p o shape stack
example {X Y : Carrier} (p : RawPolynomial) (u stack : M)
    (h : (rawCarrier X Y p).val.Evalb ![u]) :
    refill p (shape p u) (childStack p u stack) = adjoin u stack :=
  refill_shape p u stack h
