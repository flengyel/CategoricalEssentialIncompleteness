import CategoricalEssentialIncompleteness.V46NumericalDerivationWordConstructors
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46
namespace CategoricalEssentialIncompleteness.V46.NumericalSyntaxTreeChart
example (a b : SyntaxPolynomial (SyntacticPredicates.PredicateCategory 𝗧𝗔))
    (z : SyntacticLists.Obj 𝗧𝗔 ℕ
      (a.eval.obj (SyntacticSyntax.plainPostfixAlgebra 𝗧𝗔 a b).a)) :
    ((SyntacticLists.F 𝗧𝗔 ℕ).map (SyntacticSyntax.plainPostfixAlgebra 𝗧𝗔 a b).str.1 z).val =
      SyntacticSyntax.Coding.constructor false a
        (((SyntacticLists.F 𝗧𝗔 ℕ).map (plainRawInput 𝗧𝗔 a b) z).val) :=
  plainTerm_constructor_value 𝗧𝗔 a b ℕ z
end CategoricalEssentialIncompleteness.V46.NumericalSyntaxTreeChart
