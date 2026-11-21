/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxEvaluation


/-! # Finite state-and-operation records for postfix evaluation -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.EvaluationChecks
variable {T : ArithmeticTheory} {P X Y : Carrier} {a b : RawPolynomial}
variable (A : SliceAlgebra T P X Y a b)
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [M↓[ℒₒᵣ] ⊧* T]

example (p word : M) (hp : P.val.Evalb ![p]) (hw : (coefficients a b).val.Evalb ![word]) :
    ∃ states : M, A.ValueRecord p word (len word) states := A.valueRecord_exists p word hp hw

example (p word n states other : M) (hs : A.ValueRecord p word n states)
    (ho : A.ValueRecord p word n other) : nth states n = nth other n := A.valueRecord_unique hs ho

example (p word : M) (hp : P.val.Evalb ![p]) (hw : (coefficients a b).val.Evalb ![word]) :
    ∃! status : M, A.loopEvaluationGraph.val.Evalb ![p, word, status] :=
  A.loopEvaluation_existsUnique p word hp hw
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.EvaluationChecks
