import CategoricalEssentialIncompleteness.V46SyntacticSyntaxConstructorLaws

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Coding
open CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Postfix

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.ConstructorLawsChecks
variable {T : ArithmeticTheory} {P X Y : Carrier} {a b : RawPolynomial}
variable (A : SliceAlgebra T P X Y a b)
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [M↓[ℒₒᵣ] ⊧* T]

example : A.RootEquations (M := M) (A.evaluationFormula false) (A.evaluationFormula true) :=
  A.evaluation_root_equations

example (formula : Bool) (p u value : M) (hp : P.val.Evalb ![p])
    (hu : (rawCarrier (carrier false a b) (carrier true a b)
      (if formula then b else a)).val.Evalb ![u]) :
    ((A.evaluationFormula formula).val.Evalb
      ![p, constructor formula (if formula then b else a) u, value] ↔ ∃ v : M,
      (mapRaw P (A.evaluationFormula false) (A.evaluationFormula true)
        (if formula then b else a)).val.Evalb ![p, u, v] ∧
      (if formula then A.formulaOp else A.termOp).val.Evalb ![p, v, value]) :=
  A.evaluation_constructor formula p u value hp hu
end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.ConstructorLawsChecks
