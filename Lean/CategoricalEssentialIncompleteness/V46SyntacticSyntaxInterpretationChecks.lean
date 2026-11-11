/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxInterpretation


/-! # Statement checks in `V46SyntacticSyntaxInterpretationChecks` -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Postfix

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.InterpretationChecks
variable {T : ArithmeticTheory} {P X Y : Carrier} {a b : RawPolynomial}
variable (A : SliceAlgebra T P X Y a b)
section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [M↓[ℒₒᵣ] ⊧* T]
example (formula : Bool) (p word : M) (hp : P.val.Evalb ![p])
    (hw : (carrier formula a b).val.Evalb ![word]) :
    ∃! value : M, (A.evaluationFormula formula).val.Evalb ![p, word, value] :=
  A.evaluation_existsUnique formula p word hp hw
end Models
variable [𝗣𝗔 ⪯ T]
example : GraphMorphism T (productCarrier P (carrier false a b)) X := A.evaluationMorphism false
example : GraphMorphism T (productCarrier P (carrier true a b)) Y := A.evaluationMorphism true
example : T ⊢ A.evaluationOverSentence false := A.evaluation_over false
example : T ⊢ A.evaluationOverSentence true := A.evaluation_over true
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.InterpretationChecks
