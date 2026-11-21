/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalArithmeticSubstitutionParameters
public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralLogicalConstructorValues
public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralNegation

/-! # The arithmetic logical constructor squares -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.LogicalOperations
open Coordinates SubstitutionParameters NamedArithmeticSignature
local notation "S" => numericalSyntax
local notation "S₀" => originalSyntax
local notation "F" => PredicateInterpretation.functor 𝗣𝗔 ℕ
local notation "V₁" => NumericalCoordinates.codedPredicate NumericalNamed.variableObject
local notation "π₁" => LiteralSignature.coefficients relationSymbols
local notation "J" => NumericalNamed.literalFormulaPresentationIso NumericalNamed.variableObject functions relations bound

private theorem constructor_signature (u : ℕ) :
    SyntacticSyntax.Coding.constructor (M := ℕ) true
      (SyntaxPolynomial.formulaExpression V₁ π₁ bound) u =
    SyntacticSyntax.Coding.constructor (M := ℕ) true
      (SyntaxPolynomial.formulaExpression variableSymbols relationSymbols bound) u :=
  Algorithms.formulaConstructor_signature (M := ℕ) V₁ variableSymbols π₁ relationSymbols bound true u

private theorem binary_value_congr (f : ℕ → ℕ → ℕ) {x y x' y' : ℕ}
    (hx : x = x') (hy : y = y') : f x y = f x' y' := by
  cases hx
  cases hy
  rfl

private theorem rechart_projection {A X : NumericalTuples.Object}
    (C D : PredicateCategory 𝗧𝗔)
    (i : X ⟶ NumericalCoordinates.predicateObject C)
    (j : X ⟶ NumericalCoordinates.predicateObject D)
    (h : ∀ x : NumericalTuples.Point X, (i.toFun x).val = (j.toFun x).val)
    (p : A ⟶ X) (q : NumericalTuples.Point A)
    (a : PredicateInterpretation.Obj ℕ D)
    (ha : a = j.toFun (p.toFun q)) : a.val = (i.toFun (p.toFun q)).val :=
  (congrArg Subtype.val ha).trans (h (p.toFun q)).symm

private abbrev formula_value_after {A : NumericalTuples.Object}
    (p : A ⟶ (S).algebra.a.2) (q : NumericalTuples.Point A) :=
  rechart_projection ((S₀).algebra.a.2 : PredicateCategory 𝗧𝗔) sourceSyntax.algebra.a.2
    formulaIso.hom (J).hom formulaIso_value p q _ rfl

private abbrev term_value_after {A : NumericalTuples.Object}
    (p : A ⟶ (S).algebra.a.1) (q : NumericalTuples.Point A) :=
  rechart_projection ((S₀).algebra.a.1 : PredicateCategory 𝗧𝗔) sourceSyntax.algebra.a.1
    termIso.hom (NumericalNamed.literalTermPresentationIso NumericalNamed.variableObject functions relations bound).hom
    termIso_value p q _ rfl

/-- Ordered implication arguments are preserved by the product chart. -/
theorem implication_square : (S).implicationConstructor ≫ formulaIso.hom =
    (pairedIso formulaIso formulaIso).hom ≫ numericalInterpretation.map (S₀).implicationConstructor := by
  apply NumericalTuples.Map.ext
  funext q
  apply Subtype.ext
  have hn := (formula_value_after (S).implicationConstructor q).symm.trans
    ((NumericalNamed.literal_implicationConstructor_value NumericalNamed.variableObject functions relations bound q).trans
      (constructor_signature _))
  have hp := (congrArg Subtype.val (numericalInterpretation_value (C := Limits.prod (C := PredicateCategory 𝗣𝗔) (S₀).algebra.a.2 (S₀).algebra.a.2) (D := (S₀).algebra.a.2) (S₀).implicationConstructor
    ((pairedIso formulaIso formulaIso).hom.toFun q))).trans
      (NamedPlainOperationsModels.implication_value 𝗣𝗔 ℕ variableSymbols functionSymbols relationSymbols bound _)
  have hf := (congrArg Subtype.val (pairedIso_fst_point formulaIso formulaIso q)).trans
    (formula_value_after (prod.fst : (S).algebra.a.2 ⨯ (S).algebra.a.2 ⟶ (S).algebra.a.2) q).symm
  have hs := (congrArg Subtype.val (pairedIso_snd_point formulaIso formulaIso q)).trans
    (formula_value_after (prod.snd : (S).algebra.a.2 ⨯ (S).algebra.a.2 ⟶ (S).algebra.a.2) q).symm
  exact hn.trans (hp.trans (binary_value_congr
    (fun x y => SyntacticSyntax.Coding.constructor (M := ℕ) true
      (SyntaxPolynomial.formulaExpression variableSymbols relationSymbols bound)
      (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair x y) 1) 0)) hf hs)).symm

/-- Equality retains both term arguments in their original order. -/
theorem equality_square : (S).equalityConstructor ≫ formulaIso.hom =
    (pairedIso termIso termIso).hom ≫ numericalInterpretation.map (S₀).equalityConstructor := by
  apply NumericalTuples.Map.ext
  funext q
  apply Subtype.ext
  have hn := (formula_value_after (S).equalityConstructor q).symm.trans
    ((NumericalNamed.literal_equalityConstructor_value NumericalNamed.variableObject functions relations bound q).trans
      (constructor_signature _))
  have hp := (congrArg Subtype.val (numericalInterpretation_value (C := Limits.prod (C := PredicateCategory 𝗣𝗔) (S₀).algebra.a.1 (S₀).algebra.a.1) (D := (S₀).algebra.a.2) (S₀).equalityConstructor
    ((pairedIso termIso termIso).hom.toFun q))).trans
      (NamedPlainOperationsModels.equality_value 𝗣𝗔 ℕ variableSymbols functionSymbols relationSymbols bound _)
  have hf := (congrArg Subtype.val (pairedIso_fst_point termIso termIso q)).trans
    (term_value_after (prod.fst : (S).algebra.a.1 ⨯ (S).algebra.a.1 ⟶ (S).algebra.a.1) q).symm
  have hs := (congrArg Subtype.val (pairedIso_snd_point termIso termIso q)).trans
    (term_value_after (prod.snd : (S).algebra.a.1 ⨯ (S).algebra.a.1 ⟶ (S).algebra.a.1) q).symm
  exact hn.trans (hp.trans (binary_value_congr
    (fun x y => SyntacticSyntax.Coding.constructor (M := ℕ) true
      (SyntaxPolynomial.formulaExpression variableSymbols relationSymbols bound)
      (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair x y) 0) 0) 0) 0)) hf hs)).symm

/-- Generalization keeps the named binder, including names not free in its body. -/
theorem quantifier_square : (S).quantifierConstructor ≫ formulaIso.hom =
    (pairedIso variableIso formulaIso).hom ≫ numericalInterpretation.map (S₀).quantifierConstructor := by
  apply NumericalTuples.Map.ext
  funext q
  apply Subtype.ext
  have hn := (formula_value_after (S).quantifierConstructor q).symm.trans
    ((NumericalNamed.literal_quantifierConstructor_value NumericalNamed.variableObject functions relations bound q).trans
      (constructor_signature _))
  have hp := (congrArg Subtype.val (numericalInterpretation_value (C := Limits.prod (C := PredicateCategory 𝗣𝗔) variableSymbols (S₀).algebra.a.2) (D := (S₀).algebra.a.2) (S₀).quantifierConstructor
    ((pairedIso variableIso formulaIso).hom.toFun q))).trans
      (NamedPlainOperationsModels.quantifier_value 𝗣𝗔 ℕ variableSymbols functionSymbols relationSymbols bound _)
  have hf := congrArg Subtype.val (pairedIso_fst_point variableIso formulaIso q)
  have hs := (congrArg Subtype.val (pairedIso_snd_point variableIso formulaIso q)).trans
    (formula_value_after (prod.snd : NumericalNamed.variableObject ⨯ (S).algebra.a.2 ⟶ (S).algebra.a.2) q).symm
  have hx : ((F).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗣𝗔) inferInstance
      (Limits.prod (C := PredicateCategory 𝗣𝗔) variableSymbols (S₀).algebra.a.2) variableSymbols)
      ((pairedIso variableIso formulaIso).hom.toFun q)).val =
      NumericalTuples.code NumericalNamed.variableObject.dimension
        ((prod.fst : NumericalNamed.variableObject ⨯ (S).algebra.a.2 ⟶ NumericalNamed.variableObject).toFun q).val := by
    exact hf.trans (NumericalTuples.code_one _).symm
  exact hn.trans (hp.trans (binary_value_congr
    (fun x y => SyntacticSyntax.Coding.constructor (M := ℕ) true
      (SyntaxPolynomial.formulaExpression variableSymbols relationSymbols bound)
      (Arithmetic.pair (Arithmetic.pair x y) 1)) hx hs)).symm

theorem negation_square : (S).negationConstructor ≫ formulaIso.hom =
    formulaIso.hom ≫ numericalInterpretation.map (S₀).negationConstructor := by
  apply NumericalTuples.Map.ext
  funext q
  apply Subtype.ext
  have hn := (formula_value_after (S).negationConstructor q).symm.trans
    ((NumericalNamed.literal_negationConstructor_value NumericalNamed.variableObject functions relations bound q).trans
      (constructor_signature _))
  have hp := (congrArg Subtype.val (numericalInterpretation_value (C := (S₀).algebra.a.2) (D := (S₀).algebra.a.2) (S₀).negationConstructor (formulaIso.hom.toFun q))).trans
    (NamedPlainOperationsModels.negation_value 𝗣𝗔 ℕ variableSymbols functionSymbols relationSymbols bound _)
  exact hn.trans (hp.trans (congrArg (fun x : ℕ =>
    SyntacticSyntax.Coding.constructor (M := ℕ) true
      (SyntaxPolynomial.formulaExpression variableSymbols relationSymbols bound)
      (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair x 1) 0) 0)) (formulaIso_value q))).symm

end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.LogicalOperations
