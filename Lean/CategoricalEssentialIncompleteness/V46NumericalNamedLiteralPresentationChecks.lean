/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralPresentation


/-! # Statement checks in `V46NumericalNamedLiteralPresentationChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalNamedLiteralPresentationChecks
open NumericalNamed
variable (V : NumericalTuples.Object) (σ π : ℕ → NumericalTuples.Object) (d : ℕ)
local notation "S₀" => literalSourceSyntax V σ π d
local notation "a₀" => SyntaxPolynomial.termExpression (D := PredicateCategory 𝗧𝗔) (NumericalCoordinates.codedPredicate V)
  (fun n => NumericalCoordinates.codedPredicate (σ n)) d
local notation "b₀" => SyntaxPolynomial.formulaExpression (D := PredicateCategory 𝗧𝗔) (NumericalCoordinates.codedPredicate V)
  (fun n => NumericalCoordinates.codedPredicate (π n)) d

example : (literalWordAlgebra V σ π d).a =
    (NumericalCoordinates.predicateObject (literalSourceSyntax V σ π d).algebra.a.1,
      NumericalCoordinates.predicateObject (literalSourceSyntax V σ π d).algebra.a.2) := rfl

example : IsInitial (literalWordAlgebra V σ π d) := literalWordInitial V σ π d

example (P : NumericalTuples.Object) :
    IsInitial (SyntaxPolynomial.algebraWithParameters
      (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)
      (literalWordAlgebra V σ π d) P) := literalWordParameterInitial V σ π d P

example : (SyntaxPolynomial.jointFunctor (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d)).map (literalWordPairIso V σ π d).hom ≫
      (literalWordAlgebra V σ π d).str =
    (literalCategoricalSyntax V σ π d).algebra.str ≫ (literalWordPairIso V σ π d).hom :=
  literal_word_constructor_comparison V σ π d

example : (literalWordLists V σ π d).algebra.carrier =
    NumericalCoordinates.predicateObject (literalSourceSyntax V σ π d).lists.algebra.carrier := rfl

example : IsInitial (literalWordLists V σ π d).algebra.asAlgebra :=
  (literalWordLists V σ π d).initial

example (P : NumericalTuples.Object) :
    IsInitial ((literalWordLists V σ π d).algebra.withParameters P).asAlgebra :=
  (literalWordLists V σ π d).stable P

example : (literalCategoricalSyntax V σ π d).lists.algebra.nil ≫
      (literalListPresentationIso V σ π d).hom = (literalWordLists V σ π d).algebra.nil :=
  literal_word_nil_comparison V σ π d

example : (literalCategoricalSyntax V σ π d).lists.algebra.cons ≫
      (literalListPresentationIso V σ π d).hom =
    prod.map (𝟙 V) (literalListPresentationIso V σ π d).hom ≫
      (literalWordLists V σ π d).algebra.cons := literal_word_cons_comparison V σ π d

example (x : NumericalTuples.Point
    ((SyntaxPolynomial.termExpression V σ d).eval.obj (literalWordAlgebra V σ π d).a)) :
    ((literalWordAlgebra V σ π d).str.1.toFun x).val =
      SyntacticSyntax.Coding.constructor false (a₀)
        (((SyntacticLists.F 𝗧𝗔 ℕ).map (NumericalSyntaxTreeChart.plainRawInput 𝗧𝗔 (a₀) (b₀)))
          ((literalWordTermInputPresentationIso V σ π d).hom.toFun x)).val :=
  literal_wordTermConstructor_value V σ π d x

example (x : NumericalTuples.Point
    ((SyntaxPolynomial.formulaExpression V π d).eval.obj (literalWordAlgebra V σ π d).a)) :
    ((literalWordAlgebra V σ π d).str.2.toFun x).val =
      SyntacticSyntax.Coding.constructor true (b₀)
        (((SyntacticLists.F 𝗧𝗔 ℕ).map (plainFormulaRawInput 𝗧𝗔 (a₀) (b₀)))
          ((literalWordFormulaInputPresentationIso V σ π d).hom.toFun x)).val :=
  literal_wordFormulaConstructor_value V σ π d x

example
    (x : NumericalTuples.Point (V ⨯ (literalWordLists V σ π d).algebra.carrier)) :
    let x₀ := (literalWordListConsInputPresentationIso V σ π d).hom.toFun x
    ((literalWordLists V σ π d).algebra.cons.toFun x).val =
      adjoin (((PredicateInterpretation.functor 𝗧𝗔 ℕ).map
        (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
          (NumericalCoordinates.codedPredicate V ⨯ (S₀).lists.algebra.carrier)
          (NumericalCoordinates.codedPredicate V))) x₀).val
        (((PredicateInterpretation.functor 𝗧𝗔 ℕ).map
          (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance
            (NumericalCoordinates.codedPredicate V ⨯ (S₀).lists.algebra.carrier)
            (S₀).lists.algebra.carrier)) x₀).val :=
  literal_wordListCons_value V σ π d x

end CategoricalEssentialIncompleteness.V46.NumericalNamedLiteralPresentationChecks
