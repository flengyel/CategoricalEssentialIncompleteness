import CategoricalEssentialIncompleteness.V46NumericalDerivationConstructorValues
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoricalEssentialIncompleteness.V46
namespace CategoricalEssentialIncompleteness.V46.NumericalSyntaxTreeChart
variable (R : ℕ → NumericalTuples.Object) (N : ℕ)
example : (rawTreeInputIso R N).hom = rawConstructorInput R N := rawTreeInputIso_hom R N
example : (SyntacticSyntax.constructorFunctor R N).obj (treeObject R N) ≅
    NumericalCoordinates.predicateObject (treeInputPredicate R N) := treeConstructorInputIso R N
example : (literalOneSort R N).str ≫ (Iso.refl (treeObject R N)).hom =
    (treeConstructorInputIso R N).hom ≫
      NumericalCoordinates.predicateMap (oneSortRaw R N).str.1 := treeConstructor_square R N
example (x : NumericalTuples.Point ((SyntacticSyntax.constructorFunctor R N).obj (treeObject R N))) :
    ((literalOneSort R N).str.toFun x).val =
      SyntacticSyntax.Coding.constructor (M := ℕ) false (treeTermPolynomial R N)
        (((SyntacticLists.F 𝗧𝗔 ℕ).map
          (plainRawInput 𝗧𝗔 (treeTermPolynomial R N) (treeFormulaPolynomial R N))
            ((treeConstructorInputIso R N).hom.toFun x)).val) := treeConstructor_value R N x
end CategoricalEssentialIncompleteness.V46.NumericalSyntaxTreeChart
namespace CategoricalEssentialIncompleteness.V46.NumericalDerivation
open SyntacticDerivation NumericalSyntaxTreeChart
variable {F : NumericalTuples.Object} {N : ℕ} (Q : RulePresentation F N)
example : codeTreeInclusion Q ≫ (ordinaryWordAlgebraIso Q).hom.f = codeWordInclusion Q :=
  codeWordInclusion_tree Q
example : (codeAlgebra Q).str.left ≫ codeWordInclusion Q =
    InputGeometry.forget Q (codeAlgebra Q).a ≫
      (PolynomialComparison.ordinary Q).map (codeWordInclusion Q) ≫
        (literalOrdinaryTree Q).str := code_constructor_word Q
example (u : NumericalTuples.Point ((Q.inference.obj (codeAlgebra Q).a).left)) :
    ((codeAlgebra Q).str.left.toFun u).val =
      SyntacticSyntax.Coding.constructor (M := ℕ) false
        (treeTermPolynomial (PolynomialComparison.coefficients Q) N)
        (((SyntacticLists.F 𝗧𝗔 ℕ).map
          (plainRawInput 𝗧𝗔 (treeTermPolynomial (PolynomialComparison.coefficients Q) N)
            (treeFormulaPolynomial (PolynomialComparison.coefficients Q) N))
              ((treeConstructorInputIso (PolynomialComparison.coefficients Q) N).hom.toFun
                (ordinaryNodeInput Q (successfulNodeInput Q u)))).val) := code_node Q u
end CategoricalEssentialIncompleteness.V46.NumericalDerivation
