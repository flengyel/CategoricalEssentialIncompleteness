/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxState


/-! # Statement checks in `V46SyntacticSyntaxStateChecks` -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.StateChecks
variable {T : ArithmeticTheory} {P X Y : Carrier} {a b : RawPolynomial}
variable (A : SliceAlgebra T P X Y a b)
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [M↓[ℒₒᵣ] ⊧* T]

example (p record old : M) (hr : (recordCarrier a b).val.Evalb ![record])
    (hs : (statusGraph P X Y A.termProjection.graph A.formulaProjection.graph).val.Evalb ![p, old]) :
    ∃! new : M, A.valueStepGraph.val.Evalb ![p, record, old, new] :=
  A.valueStep_existsUnique p record old hr hs

example (p s stack : M) (formula : Bool)
    (hp : P.val.Evalb ![p])
    (hr : (rawCarrier zeroCarrier zeroCarrier (if formula then b else a)).val.Evalb ![s])
    (hs : (fiberStackGraph P X Y A.termProjection.graph A.formulaProjection.graph).val.Evalb ![p, stack]) :
    ∃ result : M, A.StepOutcome formula p s stack result ∧
      (statusGraph P X Y A.termProjection.graph A.formulaProjection.graph).val.Evalb ![p, result] :=
  A.stepOutcome_exists formula p s stack hp hr hs
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.StateChecks
