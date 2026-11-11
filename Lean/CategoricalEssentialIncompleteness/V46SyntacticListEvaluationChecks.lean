/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticListEvaluation

/-! Exact graph-level evaluation for arbitrary T-provable parameter fibers. -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticListEvaluation

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (P V X : Carrier) (A : SliceAlgebra T P V X)

example : GraphMorphism T (productCarrier P (listCarrier V)) X := A.evaluationMorphism

example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (p a : M)
    (hp : P.val.Evalb ![p]) (ha : (listCarrier V).val.Evalb ![a]) :
    ∃! y : M, A.evaluationFormula.val.Evalb ![p, a, y] :=
  A.evaluation_existsUnique p a hp ha

example (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (p a y : M)
    (hy : A.evaluationFormula.val.Evalb ![p, a, y]) :
    X.val.Evalb ![y] ∧ A.projection.graph.val.Evalb ![y, p] :=
  A.evaluation_fiber p a y hy

example : T ⊢ A.evaluationOverSentence := A.evaluation_over
