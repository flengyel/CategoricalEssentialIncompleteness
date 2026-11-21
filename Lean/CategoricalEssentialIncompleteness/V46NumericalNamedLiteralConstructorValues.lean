/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralValues
public import CategoricalEssentialIncompleteness.V46NumericalDerivationWordConstructors

/-! # Numerical constructors append the named postfix record -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.NumericalNamed
open SyntaxOperationsTransport

section PlainFormula
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
  (a b : SyntaxPolynomial (PredicateCategory T))

def plainFormulaRawInput : @Quiver.Hom (PredicateCategory T) inferInstance
    (b.eval.obj (SyntacticSyntax.plainPostfixAlgebra T a b).a)
    (SyntacticSyntax.rawCarrier (SyntacticSyntax.termCarrier a b)
      (SyntacticSyntax.formulaCarrier a b) b) :=
  b.eval.map (SyntacticSyntax.plainPairIso T a b).inv ≫
    representedArrow T (SyntacticSyntax.encodePolynomial T
      (SyntacticSyntax.termCarrier a b) (SyntacticSyntax.formulaCarrier a b) b)

theorem plainFormula_constructor_value (M : Type) [ORingStructure M]
    [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (z : Obj T M (b.eval.obj (SyntacticSyntax.plainPostfixAlgebra T a b).a)) :
    ((SyntacticLists.F T M).map (SyntacticSyntax.plainPostfixAlgebra T a b).str.2 z).val =
      SyntacticSyntax.Coding.constructor true b
        (((SyntacticLists.F T M).map (plainFormulaRawInput T a b) z).val) := by
  let w := (SyntacticLists.F T M).map
    (representedArrow T (SyntacticSyntax.formulaConstructorMorphism T a b))
      ((SyntacticLists.F T M).map (plainFormulaRawInput T a b) z)
  have hplain : (((SyntacticLists.F T M).map
      (SyntacticSyntax.Postfix.plainCarrierIso T true a b).hom) w).val = w.val := by
    have h := (PredicateInterpretation.map_class_eq_iff T M
      (SyntacticSyntax.Postfix.toPlainMorphism T true a b) w
      ((SyntacticLists.F T M).map
        (SyntacticSyntax.Postfix.plainCarrierIso T true a b).hom w)).mp rfl
    exact ((GraphMorphism.identityGraph_eval _ _ _).mp h).2
  have ha : (SyntacticSyntax.plainPostfixAlgebra T a b).str.2 =
      (plainFormulaRawInput T a b ≫ representedArrow T
        (SyntacticSyntax.formulaConstructorMorphism T a b)) ≫
          (SyntacticSyntax.Postfix.plainCarrierIso T true a b).hom := by
    let f := b.eval.map (SyntacticSyntax.plainPairIso T a b).inv
    let g := representedArrow T (SyntacticSyntax.encodePolynomial T
      (SyntacticSyntax.termCarrier a b) (SyntacticSyntax.formulaCarrier a b) b)
    let h := representedArrow T (SyntacticSyntax.formulaConstructorMorphism T a b)
    let k := (SyntacticSyntax.Postfix.plainCarrierIso T true a b).hom
    change f ≫ ((g ≫ h) ≫ k) = ((f ≫ g) ≫ h) ≫ k
    exact (Category.assoc f (g ≫ h) k).symm.trans
      (congrArg (fun q => q ≫ k) (Category.assoc f g h).symm)

  have h0 := congrArg (fun k => (((SyntacticLists.F T M).map k) z).val) ha
  have h1 := congrArg Subtype.val (@NumericalSyntaxTreeChart.maps_comp_apply (PredicateCategory T) inferInstance
    (SyntacticLists.F T M) _ _ _
    (plainFormulaRawInput T a b ≫ representedArrow T (SyntacticSyntax.formulaConstructorMorphism T a b))
    (SyntacticSyntax.Postfix.plainCarrierIso T true a b).hom z)
  have h2 := congrArg (fun y => (((SyntacticLists.F T M).map
    (SyntacticSyntax.Postfix.plainCarrierIso T true a b).hom) y).val)
    (@NumericalSyntaxTreeChart.maps_comp_apply (PredicateCategory T) inferInstance (SyntacticLists.F T M) _ _ _
      (plainFormulaRawInput T a b) (representedArrow T (SyntacticSyntax.formulaConstructorMorphism T a b)) z)
  exact h0.trans (h1.trans (h2.trans (hplain.trans
    (SyntacticSyntax.formulaConstructor_value T M a b
      ((SyntacticLists.F T M).map (plainFormulaRawInput T a b) z)))))

end PlainFormula

section ConstructorInputs
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) (V : D) (σ π : ℕ → D) (d : ℕ)
variable (S₀ : CategoricalSyntax (E.inverse.obj V)
  (fun n => E.inverse.obj (σ n)) (fun n => E.inverse.obj (π n)) d)
variable (S₁ : CategoricalSyntax V σ π d)
variable (c : mappedSyntaxAlgebra E V σ π d S₀ ≅ S₁.algebra)
local notation "K₀" => SyntaxPolynomial.jointFunctor
  (SyntaxPolynomial.termExpression (E.inverse.obj V) (fun n => E.inverse.obj (σ n)) d)
  (SyntaxPolynomial.formulaExpression (E.inverse.obj V) (fun n => E.inverse.obj (π n)) d)
local notation "K₁" => SyntaxPolynomial.jointFunctor
  (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)

def constructorInputPairIso : (E.prod E).functor.obj ((K₀).obj S₀.algebra.a) ≅
    (K₁).obj S₁.algebra.a :=
  (languageJointIso E V σ π d).app S₀.algebra.a ≪≫
    (K₁).mapIso (syntaxCarrierIso E V σ π d S₀ c)

def termConstructorInputIso :
    E.functor.obj ((SyntaxPolynomial.termExpression (E.inverse.obj V)
      (fun n => E.inverse.obj (σ n)) d).eval.obj S₀.algebra.a) ≅
    (SyntaxPolynomial.termExpression V σ d).eval.obj S₁.algebra.a :=
  (CategoryTheory.Prod.fst D D).mapIso (constructorInputPairIso E V σ π d S₀ S₁ c)

def formulaConstructorInputIso :
    E.functor.obj ((SyntaxPolynomial.formulaExpression (E.inverse.obj V)
      (fun n => E.inverse.obj (π n)) d).eval.obj S₀.algebra.a) ≅
    (SyntaxPolynomial.formulaExpression V π d).eval.obj S₁.algebra.a :=
  (CategoryTheory.Prod.snd D D).mapIso (constructorInputPairIso E V σ π d S₀ S₁ c)

theorem termConstructor_input_square :
    E.functor.map S₀.algebra.str.1 ≫ (syntaxTermIso («S₁» := S₁) E V σ π d S₀ c).hom =
      (termConstructorInputIso E V σ π d S₀ S₁ c).hom ≫ S₁.algebra.str.1 := by
  have h := congrArg Prod.fst (language_structure_comparison E V σ π d S₀ c)
  change E.functor.map S₀.algebra.str.1 ≫ c.hom.f.1 =
    ((languageJointIso E V σ π d).app S₀.algebra.a).hom.1 ≫
      ((K₁).map c.hom.f).1 ≫ S₁.algebra.str.1 at h
  change E.functor.map S₀.algebra.str.1 ≫ c.hom.f.1 =
    (((languageJointIso E V σ π d).app S₀.algebra.a).hom.1 ≫
      ((K₁).map c.hom.f).1) ≫ S₁.algebra.str.1
  exact h.trans (Category.assoc
    ((languageJointIso E V σ π d).app S₀.algebra.a).hom.1
    ((K₁).map c.hom.f).1 S₁.algebra.str.1).symm

theorem formulaConstructor_input_square :
    E.functor.map S₀.algebra.str.2 ≫ (syntaxFormulaIso («S₁» := S₁) E V σ π d S₀ c).hom =
      (formulaConstructorInputIso E V σ π d S₀ S₁ c).hom ≫ S₁.algebra.str.2 := by
  have h := congrArg Prod.snd (language_structure_comparison E V σ π d S₀ c)
  change E.functor.map S₀.algebra.str.2 ≫ c.hom.f.2 =
    ((languageJointIso E V σ π d).app S₀.algebra.a).hom.2 ≫
      ((K₁).map c.hom.f).2 ≫ S₁.algebra.str.2 at h
  change E.functor.map S₀.algebra.str.2 ≫ c.hom.f.2 =
    (((languageJointIso E V σ π d).app S₀.algebra.a).hom.2 ≫
      ((K₁).map c.hom.f).2) ≫ S₁.algebra.str.2
  exact h.trans (Category.assoc
    ((languageJointIso E V σ π d).app S₀.algebra.a).hom.2
    ((K₁).map c.hom.f).2 S₁.algebra.str.2).symm
end ConstructorInputs

section PresentedInputs
variable (V : NumericalTuples.Object) (σ π : ℕ → NumericalTuples.Object) (d : ℕ)
variable (R₀ : CategoricalSyntax (literalEquivalence.inverse.obj V)
  (fun n => literalEquivalence.inverse.obj (σ n))
  (fun n => literalEquivalence.inverse.obj (π n)) d)
variable (R₁ : CategoricalSyntax V σ π d)
variable (c : mappedSyntaxAlgebra literalEquivalence V σ π d R₀ ≅ R₁.algebra)

def presentedTermConstructorInputIso :
    (SyntaxPolynomial.termExpression V σ d).eval.obj R₁.algebra.a ≅
      NumericalCoordinates.predicateObject
        ((SyntaxPolynomial.termExpression (literalEquivalence.inverse.obj V)
          (fun n => literalEquivalence.inverse.obj (σ n)) d).eval.obj R₀.algebra.a) :=
  (termConstructorInputIso literalEquivalence V σ π d R₀ R₁ c).symm ≪≫
    NumericalCoordinates.predicatePresentationIso
      ((SyntaxPolynomial.termExpression (literalEquivalence.inverse.obj V)
        (fun n => literalEquivalence.inverse.obj (σ n)) d).eval.obj R₀.algebra.a)

def presentedFormulaConstructorInputIso :
    (SyntaxPolynomial.formulaExpression V π d).eval.obj R₁.algebra.a ≅
      NumericalCoordinates.predicateObject
        ((SyntaxPolynomial.formulaExpression (literalEquivalence.inverse.obj V)
          (fun n => literalEquivalence.inverse.obj (π n)) d).eval.obj R₀.algebra.a) :=
  (formulaConstructorInputIso literalEquivalence V σ π d R₀ R₁ c).symm ≪≫
    NumericalCoordinates.predicatePresentationIso
      ((SyntaxPolynomial.formulaExpression (literalEquivalence.inverse.obj V)
        (fun n => literalEquivalence.inverse.obj (π n)) d).eval.obj R₀.algebra.a)

local notation "a₀" => SyntaxPolynomial.termExpression (literalEquivalence.inverse.obj V)
  (fun n => literalEquivalence.inverse.obj (σ n)) d
local notation "b₀" => SyntaxPolynomial.formulaExpression (literalEquivalence.inverse.obj V)
  (fun n => literalEquivalence.inverse.obj (π n)) d

def presentedTermConstructorOutputIso : R₁.algebra.a.1 ≅
    NumericalCoordinates.predicateObject R₀.algebra.a.1 :=
  (syntaxTermIso («S₁» := R₁) literalEquivalence V σ π d R₀ c).symm ≪≫
    NumericalCoordinates.predicatePresentationIso R₀.algebra.a.1

def presentedFormulaConstructorOutputIso : R₁.algebra.a.2 ≅
    NumericalCoordinates.predicateObject R₀.algebra.a.2 :=
  (syntaxFormulaIso («S₁» := R₁) literalEquivalence V σ π d R₀ c).symm ≪≫
    NumericalCoordinates.predicatePresentationIso R₀.algebra.a.2

theorem presentedTermConstructor_square :
    R₁.algebra.str.1 ≫ (presentedTermConstructorOutputIso V σ π d R₀ R₁ c).hom =
      (presentedTermConstructorInputIso V σ π d R₀ R₁ c).hom ≫
        NumericalCoordinates.predicateMap R₀.algebra.str.1 :=
  conjugate_operation (literalEquivalence.functor.map R₀.algebra.str.1) R₁.algebra.str.1
    (termConstructorInputIso literalEquivalence V σ π d R₀ R₁ c)
    (syntaxTermIso («S₁» := R₁) literalEquivalence V σ π d R₀ c)
    (NumericalCoordinates.predicatePresentationIso ((a₀).eval.obj R₀.algebra.a))
    (NumericalCoordinates.predicatePresentationIso R₀.algebra.a.1)
    (termConstructor_input_square literalEquivalence V σ π d R₀ R₁ c)

theorem presentedFormulaConstructor_square :
    R₁.algebra.str.2 ≫ (presentedFormulaConstructorOutputIso V σ π d R₀ R₁ c).hom =
      (presentedFormulaConstructorInputIso V σ π d R₀ R₁ c).hom ≫
        NumericalCoordinates.predicateMap R₀.algebra.str.2 :=
  conjugate_operation (literalEquivalence.functor.map R₀.algebra.str.2) R₁.algebra.str.2
    (formulaConstructorInputIso literalEquivalence V σ π d R₀ R₁ c)
    (syntaxFormulaIso («S₁» := R₁) literalEquivalence V σ π d R₀ c)
    (NumericalCoordinates.predicatePresentationIso ((b₀).eval.obj R₀.algebra.a))
    (NumericalCoordinates.predicatePresentationIso R₀.algebra.a.2)
    (formulaConstructor_input_square literalEquivalence V σ π d R₀ R₁ c)

theorem presentedTermConstructor_value {Z : Type}
    (value : PredicateInterpretation.Obj ℕ R₀.algebra.a.1 → Z)
    (output : PredicateInterpretation.Obj ℕ ((a₀).eval.obj R₀.algebra.a) → Z)
    (hsource : ∀ a, value ((PredicateInterpretation.functor 𝗧𝗔 ℕ).map R₀.algebra.str.1 a) = output a)
    (x : NumericalTuples.Point ((SyntaxPolynomial.termExpression V σ d).eval.obj R₁.algebra.a)) :
    value ((presentedTermConstructorOutputIso V σ π d R₀ R₁ c).hom.toFun (R₁.algebra.str.1.toFun x)) =
      output ((presentedTermConstructorInputIso V σ π d R₀ R₁ c).hom.toFun x) :=
  predicate_operation_value R₀.algebra.str.1 R₁.algebra.str.1
    (presentedTermConstructorInputIso V σ π d R₀ R₁ c)
    (presentedTermConstructorOutputIso V σ π d R₀ R₁ c)
    (presentedTermConstructor_square V σ π d R₀ R₁ c) value output hsource x

theorem presentedFormulaConstructor_value {Z : Type}
    (value : PredicateInterpretation.Obj ℕ R₀.algebra.a.2 → Z)
    (output : PredicateInterpretation.Obj ℕ ((b₀).eval.obj R₀.algebra.a) → Z)
    (hsource : ∀ a, value ((PredicateInterpretation.functor 𝗧𝗔 ℕ).map R₀.algebra.str.2 a) = output a)
    (x : NumericalTuples.Point ((SyntaxPolynomial.formulaExpression V π d).eval.obj R₁.algebra.a)) :
    value ((presentedFormulaConstructorOutputIso V σ π d R₀ R₁ c).hom.toFun (R₁.algebra.str.2.toFun x)) =
      output ((presentedFormulaConstructorInputIso V σ π d R₀ R₁ c).hom.toFun x) :=
  predicate_operation_value R₀.algebra.str.2 R₁.algebra.str.2
    (presentedFormulaConstructorInputIso V σ π d R₀ R₁ c)
    (presentedFormulaConstructorOutputIso V σ π d R₀ R₁ c)
    (presentedFormulaConstructor_square V σ π d R₀ R₁ c) value output hsource x
end PresentedInputs

section LiteralValues
variable (V : NumericalTuples.Object) (σ π : ℕ → NumericalTuples.Object) (d : ℕ)
local notation "E" => literalEquivalence
local notation "S₀" => literalSourceSyntax V σ π d
local notation "S₁" => literalCategoricalSyntax V σ π d
local notation "a" => SyntaxPolynomial.termExpression (NumericalCoordinates.codedPredicate V)
  (fun n => NumericalCoordinates.codedPredicate (σ n)) d
local notation "b" => SyntaxPolynomial.formulaExpression (NumericalCoordinates.codedPredicate V)
  (fun n => NumericalCoordinates.codedPredicate (π n)) d

def literalTermConstructorInputPresentationIso :=
  presentedTermConstructorInputIso V σ π d (S₀) (S₁) (literalAlgebraIso V σ π d)

def literalFormulaConstructorInputPresentationIso :=
  presentedFormulaConstructorInputIso V σ π d (S₀) (S₁) (literalAlgebraIso V σ π d)

abbrev literal_termConstructor_code_square :=
  presentedTermConstructor_square V σ π d (S₀) (S₁) (literalAlgebraIso V σ π d)

abbrev literal_formulaConstructor_code_square :=
  presentedFormulaConstructor_square V σ π d (S₀) (S₁) (literalAlgebraIso V σ π d)

theorem literal_termConstructor_value (x : NumericalTuples.Point
    ((SyntaxPolynomial.termExpression V σ d).eval.obj (S₁).algebra.a)) :
    ((literalTermPresentationIso V σ π d).hom.toFun ((S₁).algebra.str.1.toFun x)).val =
      SyntacticSyntax.Coding.constructor false (a)
        (((F 𝗧𝗔 ℕ).map (NumericalSyntaxTreeChart.plainRawInput 𝗧𝗔 (a) (b)))
          ((literalTermConstructorInputPresentationIso V σ π d).hom.toFun x)).val :=
  presentedTermConstructor_value V σ π d (S₀) (S₁) (literalAlgebraIso V σ π d) Subtype.val _
    (NumericalSyntaxTreeChart.plainTerm_constructor_value 𝗧𝗔 (a) (b) ℕ) x

theorem literal_formulaConstructor_value (x : NumericalTuples.Point
    ((SyntaxPolynomial.formulaExpression V π d).eval.obj (S₁).algebra.a)) :
    ((literalFormulaPresentationIso V σ π d).hom.toFun ((S₁).algebra.str.2.toFun x)).val =
      SyntacticSyntax.Coding.constructor true (b)
        (((F 𝗧𝗔 ℕ).map (plainFormulaRawInput 𝗧𝗔 (a) (b)))
          ((literalFormulaConstructorInputPresentationIso V σ π d).hom.toFun x)).val :=
  presentedFormulaConstructor_value V σ π d (S₀) (S₁) (literalAlgebraIso V σ π d) Subtype.val _
    (plainFormula_constructor_value 𝗧𝗔 (a) (b) ℕ) x
end LiteralValues
end CategoricalEssentialIncompleteness.V46.NumericalNamed
