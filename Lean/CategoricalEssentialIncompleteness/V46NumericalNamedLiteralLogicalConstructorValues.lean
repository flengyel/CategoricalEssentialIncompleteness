/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralInputValues
public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralConstructorValues
public import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportConstructorsFormula
public import CategoricalEssentialIncompleteness.V46NamedPlainOperationsModels

/-! # Literal values of the numerical logical constructors -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalNamed
open SyntaxOperationsTransport
local notation "E" => literalEquivalence
local notation "F" => PredicateInterpretation.functor 𝗧𝗔 ℕ

section Presented
variable (V : NumericalTuples.Object) (σ π : ℕ → NumericalTuples.Object) (d : ℕ)
variable (R₀ : CategoricalSyntax ((E).inverse.obj V)
  (fun n => (E).inverse.obj (σ n)) (fun n => (E).inverse.obj (π n)) d)
variable (R₁ : CategoricalSyntax V σ π d)
variable (c : mappedSyntaxAlgebra (E) V σ π d R₀ ≅ R₁.algebra)

def presentedImplicationInputIso : R₁.algebra.a.2 ⨯ R₁.algebra.a.2 ≅
    NumericalCoordinates.predicateObject (R₀.algebra.a.2 ⨯ R₀.algebra.a.2) :=
  @presentedProductIso (R₀.algebra.a.2) (R₀.algebra.a.2) (R₁.algebra.a.2) (R₁.algebra.a.2) (syntaxFormulaIso («S₁» := R₁) (E) V σ π d R₀ c) (syntaxFormulaIso («S₁» := R₁) (E) V σ π d R₀ c)

theorem presentedImplication_square :
    R₁.implicationConstructor ≫ (presentedFormulaConstructorOutputIso V σ π d R₀ R₁ c).hom =
      (presentedImplicationInputIso V σ π d R₀ R₁ c).hom ≫
        NumericalCoordinates.predicateMap R₀.implicationConstructor :=
  conjugate_operation ((E).functor.map R₀.implicationConstructor) R₁.implicationConstructor
    (SyntaxOptionTransport.productIso (E) (syntaxFormulaIso («S₁» := R₁) (E) V σ π d R₀ c) (syntaxFormulaIso («S₁» := R₁) (E) V σ π d R₀ c))
    (syntaxFormulaIso («S₁» := R₁) (E) V σ π d R₀ c)
    (NumericalCoordinates.predicatePresentationIso (R₀.algebra.a.2 ⨯ R₀.algebra.a.2))
    (NumericalCoordinates.predicatePresentationIso R₀.algebra.a.2)
    (syntax_implication_constructor (E) V σ π d R₀ R₁ c)

theorem presentedImplication_value {Z : Type}
    (value : PredicateInterpretation.Obj ℕ R₀.algebra.a.2 → Z)
    (output : PredicateInterpretation.Obj ℕ (Limits.prod (C := PredicateCategory 𝗧𝗔) (R₀.algebra.a.2) (R₀.algebra.a.2)) → Z)
    (hsource : ∀ x, value ((F).map R₀.implicationConstructor x) = output x)
    (x : NumericalTuples.Point (R₁.algebra.a.2 ⨯ R₁.algebra.a.2)) :
    value ((presentedFormulaConstructorOutputIso V σ π d R₀ R₁ c).hom.toFun
      (R₁.implicationConstructor.toFun x)) =
        output ((presentedImplicationInputIso V σ π d R₀ R₁ c).hom.toFun x) :=
  predicate_operation_value R₀.implicationConstructor R₁.implicationConstructor
    (presentedImplicationInputIso V σ π d R₀ R₁ c)
    (presentedFormulaConstructorOutputIso V σ π d R₀ R₁ c)
    (presentedImplication_square V σ π d R₀ R₁ c) value output hsource x

def presentedEqualityInputIso : R₁.algebra.a.1 ⨯ R₁.algebra.a.1 ≅
    NumericalCoordinates.predicateObject (R₀.algebra.a.1 ⨯ R₀.algebra.a.1) :=
  @presentedProductIso (R₀.algebra.a.1) (R₀.algebra.a.1) (R₁.algebra.a.1) (R₁.algebra.a.1) (syntaxTermIso («S₁» := R₁) (E) V σ π d R₀ c) (syntaxTermIso («S₁» := R₁) (E) V σ π d R₀ c)

theorem presentedEquality_square :
    R₁.equalityConstructor ≫ (presentedFormulaConstructorOutputIso V σ π d R₀ R₁ c).hom =
      (presentedEqualityInputIso V σ π d R₀ R₁ c).hom ≫
        NumericalCoordinates.predicateMap R₀.equalityConstructor :=
  conjugate_operation ((E).functor.map R₀.equalityConstructor) R₁.equalityConstructor
    (SyntaxOptionTransport.productIso (E) (syntaxTermIso («S₁» := R₁) (E) V σ π d R₀ c) (syntaxTermIso («S₁» := R₁) (E) V σ π d R₀ c))
    (syntaxFormulaIso («S₁» := R₁) (E) V σ π d R₀ c)
    (NumericalCoordinates.predicatePresentationIso (R₀.algebra.a.1 ⨯ R₀.algebra.a.1))
    (NumericalCoordinates.predicatePresentationIso R₀.algebra.a.2)
    (syntax_equality_constructor (E) V σ π d R₀ R₁ c)

theorem presentedEquality_value {Z : Type}
    (value : PredicateInterpretation.Obj ℕ R₀.algebra.a.2 → Z)
    (output : PredicateInterpretation.Obj ℕ (Limits.prod (C := PredicateCategory 𝗧𝗔) (R₀.algebra.a.1) (R₀.algebra.a.1)) → Z)
    (hsource : ∀ x, value ((F).map R₀.equalityConstructor x) = output x)
    (x : NumericalTuples.Point (R₁.algebra.a.1 ⨯ R₁.algebra.a.1)) :
    value ((presentedFormulaConstructorOutputIso V σ π d R₀ R₁ c).hom.toFun
      (R₁.equalityConstructor.toFun x)) =
        output ((presentedEqualityInputIso V σ π d R₀ R₁ c).hom.toFun x) :=
  predicate_operation_value R₀.equalityConstructor R₁.equalityConstructor
    (presentedEqualityInputIso V σ π d R₀ R₁ c)
    (presentedFormulaConstructorOutputIso V σ π d R₀ R₁ c)
    (presentedEquality_square V σ π d R₀ R₁ c) value output hsource x

def presentedQuantifierInputIso : V ⨯ R₁.algebra.a.2 ≅
    NumericalCoordinates.predicateObject ((E).inverse.obj V ⨯ R₀.algebra.a.2) :=
  @presentedProductIso ((E).inverse.obj V) (R₀.algebra.a.2) (V) (R₁.algebra.a.2) ((E).counitIso.app V) (syntaxFormulaIso («S₁» := R₁) (E) V σ π d R₀ c)

theorem presentedQuantifier_square :
    R₁.quantifierConstructor ≫ (presentedFormulaConstructorOutputIso V σ π d R₀ R₁ c).hom =
      (presentedQuantifierInputIso V σ π d R₀ R₁ c).hom ≫
        NumericalCoordinates.predicateMap R₀.quantifierConstructor :=
  conjugate_operation ((E).functor.map R₀.quantifierConstructor) R₁.quantifierConstructor
    (SyntaxOptionTransport.productIso (E) ((E).counitIso.app V) (syntaxFormulaIso («S₁» := R₁) (E) V σ π d R₀ c))
    (syntaxFormulaIso («S₁» := R₁) (E) V σ π d R₀ c)
    (NumericalCoordinates.predicatePresentationIso ((E).inverse.obj V ⨯ R₀.algebra.a.2))
    (NumericalCoordinates.predicatePresentationIso R₀.algebra.a.2)
    (syntax_quantifier_constructor (E) V σ π d R₀ R₁ c)

theorem presentedQuantifier_value {Z : Type}
    (value : PredicateInterpretation.Obj ℕ R₀.algebra.a.2 → Z)
    (output : PredicateInterpretation.Obj ℕ (Limits.prod (C := PredicateCategory 𝗧𝗔) ((E).inverse.obj V) (R₀.algebra.a.2)) → Z)
    (hsource : ∀ x, value ((F).map R₀.quantifierConstructor x) = output x)
    (x : NumericalTuples.Point (V ⨯ R₁.algebra.a.2)) :
    value ((presentedFormulaConstructorOutputIso V σ π d R₀ R₁ c).hom.toFun
      (R₁.quantifierConstructor.toFun x)) =
        output ((presentedQuantifierInputIso V σ π d R₀ R₁ c).hom.toFun x) :=
  predicate_operation_value R₀.quantifierConstructor R₁.quantifierConstructor
    (presentedQuantifierInputIso V σ π d R₀ R₁ c)
    (presentedFormulaConstructorOutputIso V σ π d R₀ R₁ c)
    (presentedQuantifier_square V σ π d R₀ R₁ c) value output hsource x
end Presented

section Actual
variable (V : NumericalTuples.Object) (σ π : ℕ → NumericalTuples.Object) (d : ℕ)
local notation "S₀" => literalSourceSyntax V σ π d
local notation "S₁" => literalCategoricalSyntax V σ π d
local notation "V₀" => NumericalCoordinates.codedPredicate V
local notation "σ₀" => (fun n => NumericalCoordinates.codedPredicate (σ n))
local notation "π₀" => (fun n => NumericalCoordinates.codedPredicate (π n))

def literalImplicationInputPresentationIso :=
  presentedImplicationInputIso V σ π d (S₀) (S₁) (literalAlgebraIso V σ π d)

abbrev literal_implicationConstructor_code_square :=
  presentedImplication_square V σ π d (S₀) (S₁) (literalAlgebraIso V σ π d)

abbrev literal_implication_input_fst :=
  @presentedProduct_fst_value ((S₀).algebra.a.2) ((S₀).algebra.a.2) ((S₁).algebra.a.2) ((S₁).algebra.a.2) (literalFormulaIso V σ π d) (literalFormulaIso V σ π d)

abbrev literal_implication_input_snd :=
  @presentedProduct_snd_value ((S₀).algebra.a.2) ((S₀).algebra.a.2) ((S₁).algebra.a.2) ((S₁).algebra.a.2) (literalFormulaIso V σ π d) (literalFormulaIso V σ π d)

def literalEqualityInputPresentationIso :=
  presentedEqualityInputIso V σ π d (S₀) (S₁) (literalAlgebraIso V σ π d)

abbrev literal_equalityConstructor_code_square :=
  presentedEquality_square V σ π d (S₀) (S₁) (literalAlgebraIso V σ π d)

abbrev literal_equality_input_fst :=
  @presentedProduct_fst_value ((S₀).algebra.a.1) ((S₀).algebra.a.1) ((S₁).algebra.a.1) ((S₁).algebra.a.1) (literalTermIso V σ π d) (literalTermIso V σ π d)

abbrev literal_equality_input_snd :=
  @presentedProduct_snd_value ((S₀).algebra.a.1) ((S₀).algebra.a.1) ((S₁).algebra.a.1) ((S₁).algebra.a.1) (literalTermIso V σ π d) (literalTermIso V σ π d)

def literalQuantifierInputPresentationIso :=
  presentedQuantifierInputIso V σ π d (S₀) (S₁) (literalAlgebraIso V σ π d)

abbrev literal_quantifierConstructor_code_square :=
  presentedQuantifier_square V σ π d (S₀) (S₁) (literalAlgebraIso V σ π d)

abbrev literal_quantifier_input_fst :=
  @presentedProduct_fst_value (V₀) ((S₀).algebra.a.2) (V) ((S₁).algebra.a.2) ((E).counitIso.app V) (literalFormulaIso V σ π d)

abbrev literal_quantifier_input_snd :=
  @presentedProduct_snd_value (V₀) ((S₀).algebra.a.2) (V) ((S₁).algebra.a.2) ((E).counitIso.app V) (literalFormulaIso V σ π d)

theorem literal_implicationConstructor_source_value (q : NumericalTuples.Point ((S₁).algebra.a.2 ⨯ (S₁).algebra.a.2)) :
    let q₀ := (literalImplicationInputPresentationIso V σ π d).hom.toFun q
    ((literalFormulaPresentationIso V σ π d).hom.toFun ((S₁).implicationConstructor.toFun q)).val =
      SyntacticSyntax.Coding.constructor (M := ℕ) true (SyntaxPolynomial.formulaExpression V₀ π₀ d)
        (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair ((((F).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance ((S₀).algebra.a.2 ⨯ (S₀).algebra.a.2) ((S₀).algebra.a.2))) q₀).val) ((((F).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance ((S₀).algebra.a.2 ⨯ (S₀).algebra.a.2) ((S₀).algebra.a.2))) q₀).val)) 1) 0) :=
  presentedImplication_value V σ π d (S₀) (S₁) (literalAlgebraIso V σ π d) Subtype.val _
    (NamedPlainOperationsModels.implication_value 𝗧𝗔 ℕ V₀ σ₀ π₀ d) q

theorem literal_implicationConstructor_value (q : NumericalTuples.Point ((S₁).algebra.a.2 ⨯ (S₁).algebra.a.2)) :
    ((literalFormulaPresentationIso V σ π d).hom.toFun ((S₁).implicationConstructor.toFun q)).val =
      SyntacticSyntax.Coding.constructor (M := ℕ) true (SyntaxPolynomial.formulaExpression V₀ π₀ d)
        (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair (((literalFormulaPresentationIso V σ π d).hom.toFun ((prod.fst : (S₁).algebra.a.2 ⨯ (S₁).algebra.a.2 ⟶ (S₁).algebra.a.2).toFun q)).val) (((literalFormulaPresentationIso V σ π d).hom.toFun ((prod.snd : (S₁).algebra.a.2 ⨯ (S₁).algebra.a.2 ⟶ (S₁).algebra.a.2).toFun q)).val)) 1) 0) := by
  have hf := congrArg Subtype.val (literal_implication_input_fst V σ π d q)
  have hs := congrArg Subtype.val (literal_implication_input_snd V σ π d q)
  exact (literal_implicationConstructor_source_value V σ π d q).trans
    (congrArg₂ (fun a b : ℕ => SyntacticSyntax.Coding.constructor (M := ℕ) true
      (SyntaxPolynomial.formulaExpression V₀ π₀ d) (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair a b) 1) 0)) hf hs)

theorem literal_equalityConstructor_source_value (q : NumericalTuples.Point ((S₁).algebra.a.1 ⨯ (S₁).algebra.a.1)) :
    let q₀ := (literalEqualityInputPresentationIso V σ π d).hom.toFun q
    ((literalFormulaPresentationIso V σ π d).hom.toFun ((S₁).equalityConstructor.toFun q)).val =
      SyntacticSyntax.Coding.constructor (M := ℕ) true (SyntaxPolynomial.formulaExpression V₀ π₀ d)
        (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair ((((F).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance ((S₀).algebra.a.1 ⨯ (S₀).algebra.a.1) ((S₀).algebra.a.1))) q₀).val) ((((F).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance ((S₀).algebra.a.1 ⨯ (S₀).algebra.a.1) ((S₀).algebra.a.1))) q₀).val)) 0) 0) 0) 0) :=
  presentedEquality_value V σ π d (S₀) (S₁) (literalAlgebraIso V σ π d) Subtype.val _
    (NamedPlainOperationsModels.equality_value 𝗧𝗔 ℕ V₀ σ₀ π₀ d) q

theorem literal_equalityConstructor_value (q : NumericalTuples.Point ((S₁).algebra.a.1 ⨯ (S₁).algebra.a.1)) :
    ((literalFormulaPresentationIso V σ π d).hom.toFun ((S₁).equalityConstructor.toFun q)).val =
      SyntacticSyntax.Coding.constructor (M := ℕ) true (SyntaxPolynomial.formulaExpression V₀ π₀ d)
        (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair (((literalTermPresentationIso V σ π d).hom.toFun ((prod.fst : (S₁).algebra.a.1 ⨯ (S₁).algebra.a.1 ⟶ (S₁).algebra.a.1).toFun q)).val) (((literalTermPresentationIso V σ π d).hom.toFun ((prod.snd : (S₁).algebra.a.1 ⨯ (S₁).algebra.a.1 ⟶ (S₁).algebra.a.1).toFun q)).val)) 0) 0) 0) 0) := by
  have hf := congrArg Subtype.val (literal_equality_input_fst V σ π d q)
  have hs := congrArg Subtype.val (literal_equality_input_snd V σ π d q)
  exact (literal_equalityConstructor_source_value V σ π d q).trans
    (congrArg₂ (fun a b : ℕ => SyntacticSyntax.Coding.constructor (M := ℕ) true
      (SyntaxPolynomial.formulaExpression V₀ π₀ d) (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair (Arithmetic.pair a b) 0) 0) 0) 0)) hf hs)

theorem literal_quantifierConstructor_source_value (q : NumericalTuples.Point (V ⨯ (S₁).algebra.a.2)) :
    let q₀ := (literalQuantifierInputPresentationIso V σ π d).hom.toFun q
    ((literalFormulaPresentationIso V σ π d).hom.toFun ((S₁).quantifierConstructor.toFun q)).val =
      SyntacticSyntax.Coding.constructor (M := ℕ) true (SyntaxPolynomial.formulaExpression V₀ π₀ d)
        (Arithmetic.pair (Arithmetic.pair ((((F).map (prod.fst : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance (V₀ ⨯ (S₀).algebra.a.2) (V₀))) q₀).val) ((((F).map (prod.snd : @Quiver.Hom (PredicateCategory 𝗧𝗔) inferInstance (V₀ ⨯ (S₀).algebra.a.2) ((S₀).algebra.a.2))) q₀).val)) 1) :=
  presentedQuantifier_value V σ π d (S₀) (S₁) (literalAlgebraIso V σ π d) Subtype.val _
    (NamedPlainOperationsModels.quantifier_value 𝗧𝗔 ℕ V₀ σ₀ π₀ d) q

theorem literal_quantifierConstructor_value (q : NumericalTuples.Point (V ⨯ (S₁).algebra.a.2)) :
    ((literalFormulaPresentationIso V σ π d).hom.toFun ((S₁).quantifierConstructor.toFun q)).val =
      SyntacticSyntax.Coding.constructor (M := ℕ) true (SyntaxPolynomial.formulaExpression V₀ π₀ d)
        (Arithmetic.pair (Arithmetic.pair (NumericalTuples.code V.dimension ((prod.fst : V ⨯ (S₁).algebra.a.2 ⟶ V).toFun q).val) (((literalFormulaPresentationIso V σ π d).hom.toFun ((prod.snd : V ⨯ (S₁).algebra.a.2 ⟶ (S₁).algebra.a.2).toFun q)).val)) 1) := by
  have hf := congrArg Subtype.val (literal_quantifier_input_fst V σ π d q)
  have hs := congrArg Subtype.val (literal_quantifier_input_snd V σ π d q)
  have hn := hf.trans (literalVariablePresentation_value V ((prod.fst : V ⨯ (S₁).algebra.a.2 ⟶ V).toFun q))
  exact (literal_quantifierConstructor_source_value V σ π d q).trans
    (congrArg₂ (fun a b : ℕ => SyntacticSyntax.Coding.constructor (M := ℕ) true
      (SyntaxPolynomial.formulaExpression V₀ π₀ d) (Arithmetic.pair (Arithmetic.pair a b) 1)) hn hs)
end Actual
end CategoricalEssentialIncompleteness.V46.NumericalNamed
