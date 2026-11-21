/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralLogicalConstructorValues


/-! # Literal values of the numerical logical constructors -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.NumericalNamedLiteralLogicalConstructorValuesChecks
open NumericalNamed
variable (V : NumericalTuples.Object) (σ π : ℕ → NumericalTuples.Object) (d : ℕ)
local notation "S₁" => literalCategoricalSyntax V σ π d
local notation "V₀" => NumericalCoordinates.codedPredicate V
local notation "π₀" => (fun n => NumericalCoordinates.codedPredicate (π n))
example (q : NumericalTuples.Point ((S₁).algebra.a.2 ⨯ (S₁).algebra.a.2)) :
    ((literalFormulaPresentationIso V σ π d).hom.toFun ((S₁).implicationConstructor.toFun q)).val =
      SyntacticSyntax.Coding.constructor (M := ℕ) true (SyntaxPolynomial.formulaExpression V₀ π₀ d)
        (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair (((literalFormulaPresentationIso V σ π d).hom.toFun ((prod.fst : (S₁).algebra.a.2 ⨯ (S₁).algebra.a.2 ⟶ (S₁).algebra.a.2).toFun q)).val) (((literalFormulaPresentationIso V σ π d).hom.toFun ((prod.snd : (S₁).algebra.a.2 ⨯ (S₁).algebra.a.2 ⟶ (S₁).algebra.a.2).toFun q)).val)) 1) 0) :=
  literal_implicationConstructor_value V σ π d q

example (q : NumericalTuples.Point ((S₁).algebra.a.1 ⨯ (S₁).algebra.a.1)) :
    ((literalFormulaPresentationIso V σ π d).hom.toFun ((S₁).equalityConstructor.toFun q)).val =
      SyntacticSyntax.Coding.constructor (M := ℕ) true (SyntaxPolynomial.formulaExpression V₀ π₀ d)
        (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair (((literalTermPresentationIso V σ π d).hom.toFun ((prod.fst : (S₁).algebra.a.1 ⨯ (S₁).algebra.a.1 ⟶ (S₁).algebra.a.1).toFun q)).val) (((literalTermPresentationIso V σ π d).hom.toFun ((prod.snd : (S₁).algebra.a.1 ⨯ (S₁).algebra.a.1 ⟶ (S₁).algebra.a.1).toFun q)).val)) 0) 0) 0) 0) :=
  literal_equalityConstructor_value V σ π d q

example (q : NumericalTuples.Point (V ⨯ (S₁).algebra.a.2)) :
    ((literalFormulaPresentationIso V σ π d).hom.toFun ((S₁).quantifierConstructor.toFun q)).val =
      SyntacticSyntax.Coding.constructor (M := ℕ) true (SyntaxPolynomial.formulaExpression V₀ π₀ d)
        (Arithmetic.pair (Arithmetic.pair (NumericalTuples.code V.dimension ((prod.fst : V ⨯ (S₁).algebra.a.2 ⟶ V).toFun q).val) (((literalFormulaPresentationIso V σ π d).hom.toFun ((prod.snd : V ⨯ (S₁).algebra.a.2 ⟶ (S₁).algebra.a.2).toFun q)).val)) 1) :=
  literal_quantifierConstructor_value V σ π d q

end CategoricalEssentialIncompleteness.V46.NumericalNamedLiteralLogicalConstructorValuesChecks
