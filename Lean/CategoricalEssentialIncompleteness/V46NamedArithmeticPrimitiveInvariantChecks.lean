import CategoricalEssentialIncompleteness.V46NamedArithmeticPrimitiveInvariant
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.NamedArithmeticPrimitiveRecursion
example {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    {p : PR.Blueprint 0} (c : PR.Construction M p) (C : Carrier)
    (hz : C.val.Evalb ![c.zero ![]])
    (hs : ∀ n previous : M, C.val.Evalb ![previous] →
      C.val.Evalb ![c.succ ![] n previous]) :
    ∀ n : M, C.val.Evalb ![scalarResult c n] :=
  scalarResult_carrier c C hz hs
