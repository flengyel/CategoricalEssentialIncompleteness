import CategoricalEssentialIncompleteness.V46SyntacticSyntaxEvaluationLaws

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Postfix

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.EvaluationLawsChecks
variable {T : ArithmeticTheory} {P X Y : Carrier} {a b : RawPolynomial}
variable (A : SliceAlgebra T P X Y a b)
section Models
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [M↓[ℒₒᵣ] ⊧* T]

example (formula : Bool) (p word : M) (hp : P.val.Evalb ![p])
    (hw : (carrier formula a b).val.Evalb ![word]) :
    ∃! value : M, (A.evaluationFormula formula).val.Evalb ![p, word, value] :=
  A.evaluation_existsUnique formula p word hp hw

example (formula : Bool) (p u value : M) (hp : P.val.Evalb ![p])
    (hu : (rawCarrier (carrier false a b) (carrier true a b)
      (if formula then b else a)).val.Evalb ![u]) :
    ((A.evaluationFormula formula).val.Evalb
      ![p, constructor formula (if formula then b else a) u, value] ↔ ∃ v : M,
      (mapRaw P (A.evaluationFormula false) (A.evaluationFormula true)
        (if formula then b else a)).val.Evalb ![p, u, v] ∧
      (if formula then A.formulaOp else A.termOp).val.Evalb ![p, v, value]) :=
  A.evaluation_constructor formula p u value hp hu

example (hT hF : TernaryGraph) (hroot : A.RootEquations (M := M) hT hF)
    (formula : Bool) (p word x y : M)
    (hx : (if formula then hF else hT).val.Evalb ![p, word, x])
    (hy : (A.evaluationFormula formula).val.Evalb ![p, word, y]) : x = y :=
  A.evaluation_unique hT hF hroot formula p word x y hx hy
end Models

variable [𝗣𝗔 ⪯ T]
example : GraphMorphism T (productCarrier P (carrier false a b)) X := A.evaluationMorphism false
example : GraphMorphism T (productCarrier P (carrier true a b)) Y := A.evaluationMorphism true
example : T ⊢ A.evaluationOverSentence false := A.evaluation_over false
example : T ⊢ A.evaluationOverSentence true := A.evaluation_over true
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.EvaluationLawsChecks
