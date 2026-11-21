/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxRawEvaluation


/-! # Finite-polynomial action on literal-word evaluation graphs -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Postfix

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.RawEvaluationChecks
variable {T : ArithmeticTheory} {P X Y : Carrier} {a b : RawPolynomial}
variable (A : SliceAlgebra T P X Y a b)
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]

example (q : RawPolynomial) (p u v : M)
    (h : (mapRaw P (A.evaluationFormula false) (A.evaluationFormula true) q).val.Evalb ![p, u, v]) :
    P.val.Evalb ![p] ∧
      (rawCarrier (carrier false a b) (carrier true a b) q).val.Evalb ![u] ∧
      (rawFiber P X Y A.termProjection.graph A.formulaProjection.graph q).val.Evalb ![p, v] :=
  A.mapRaw_evaluation_fiber q p u v h

example [M↓[ℒₒᵣ] ⊧* T] (q : RawPolynomial) (p u : M)
    (hp : P.val.Evalb ![p])
    (hu : (rawCarrier (carrier false a b) (carrier true a b) q).val.Evalb ![u]) :
    ∃ v : M, (mapRaw P (A.evaluationFormula false) (A.evaluationFormula true) q).val.Evalb ![p, u, v] :=
  A.mapRaw_evaluation_exists q p u hp hu
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.RawEvaluationChecks
