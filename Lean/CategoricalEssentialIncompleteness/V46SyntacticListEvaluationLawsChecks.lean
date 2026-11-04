import CategoricalEssentialIncompleteness.V46SyntacticListEvaluationLaws

/-! Nil/cons equations and uniqueness against arbitrary represented candidates. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticListEvaluation
open CategoricalEssentialIncompleteness.V46.SyntacticListEvaluation.SliceAlgebra

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (P V X : Carrier) (A : SliceAlgebra T P V X)

example : T ⊢ A.nilEquationSentence := A.evaluation_nil_equation

example : T ⊢ A.consEquationSentence := A.evaluation_cons_equation

example (H : GraphMorphism T (productCarrier P (listCarrier V)) X)
    (hn : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (p y : M),
      (unpackedGraph H.graph).val.Evalb ![p, 0, y] ↔ A.nilOp.graph.val.Evalb ![p, y])
    (hc : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
      (p v a y : M), (unpackedGraph H.graph).val.Evalb ![p, adjoin v a, y] ↔
        V.val.Evalb ![v] ∧ ∃ x : M, (unpackedGraph H.graph).val.Evalb ![p, a, x] ∧
          A.consOp.val.Evalb ![p, v, x, y]) :
    representedArrow T H = representedArrow T A.evaluationMorphism :=
  A.evaluation_unique H hn hc
