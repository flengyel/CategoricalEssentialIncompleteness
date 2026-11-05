import CategoricalEssentialIncompleteness.V46SyntacticSyntaxChildrenTrace

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.ChildrenTraceChecks
variable {T : ArithmeticTheory} {P X Y : Carrier} {a b : RawPolynomial}
variable (A : SliceAlgebra T P X Y a b)
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

example (q : RawPolynomial) (p u v tail : M)
    (hp : P.val.Evalb ![p])
    (hm : (mapRaw P (A.evaluationFormula false) (A.evaluationFormula true) q).val.Evalb ![p, u, v])
    (ht : (fiberStackGraph P X Y A.termProjection.graph A.formulaProjection.graph).val.Evalb ![p, tail]) :
    ∃ states : M,
      A.TraceRecord p (childrenWord q u) (tail + 1) (len (childrenWord q u)) states ∧
        nth states (len (childrenWord q u)) = childStack q v tail + 1 :=
  A.children_trace q p u v tail hp hm ht

end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.ChildrenTraceChecks
