import CategoricalEssentialIncompleteness.V46NamedPlainConstructorModels

noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.NamedPlainConstructorModelsChecks
open SyntacticSyntax NamedPlainConstructorModels
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
variable (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
example (a b : SyntaxPolynomial (PredicateCategory T)) (u : M)
    (z : Obj T M (a.eval.obj (plainPostfixAlgebra T a b).a))
    (h : (baseRepresentation T (Postfix.plainCarrier false a b)
      (Postfix.plainCarrier true a b) a).val.Evalb ![u,z.val]) :
    ((F T M).map (plainPostfixAlgebra T a b).str.1 z).val = Coding.constructor false a u :=
  plainTerm_value T M a b u z h
example (a b : SyntaxPolynomial (PredicateCategory T)) (u : M)
    (z : Obj T M (b.eval.obj (plainPostfixAlgebra T a b).a))
    (h : (baseRepresentation T (Postfix.plainCarrier false a b)
      (Postfix.plainCarrier true a b) b).val.Evalb ![u,z.val]) :
    ((F T M).map (plainPostfixAlgebra T a b).str.2 z).val = Coding.constructor true b u :=
  plainFormula_value T M a b u z h
end CategoricalEssentialIncompleteness.V46.NamedPlainConstructorModelsChecks
