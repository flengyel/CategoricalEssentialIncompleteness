/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalArithmeticCoordinates
public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralConstructorValues
public import CategoricalEssentialIncompleteness.V46NumericalPolynomialRepresentation
public import CategoricalEssentialIncompleteness.V46NumericalDerivationInterpretationPlain

/-! # The actual arithmetic coefficient and polynomial-input charts -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.SyntaxTemplate
open Coordinates NamedArithmeticSignature SyntacticSyntax
abbrev E := NumericalSyntaxTreeChart.E

/-- Roles remain distinct even if two coefficient predicates happen to coincide. -/
inductive Label
  | name
  | function (arity : ℕ)
  | relation (arity : ℕ)

def source : Label → PredicateCategory 𝗣𝗔
  | .name => variableSymbols
  | .function k => functionSymbols k
  | .relation k => relationSymbols k

def target : Label → PredicateCategory 𝗧𝗔
  | .name => NumericalCoordinates.codedPredicate NumericalNamed.variableObject
  | .function k => LiteralSignature.coefficients functionSymbols k
  | .relation k => LiteralSignature.coefficients relationSymbols k

def coefficientChart : ∀ i, numericalInterpretation.obj (source i) ≅ E.functor.obj (target i)
  | .name => variableIso.symm ≪≫ (E.counitIso.app NumericalNamed.variableObject).symm
  | .function k => (E.counitIso.app (functions k)).symm
  | .relation k => (E.counitIso.app (relations k)).symm

theorem coefficient_value (i : Label) (z : Obj 𝗣𝗔 ℕ (source i)) :
    ((NumericalCoordinates.predicatePresentationIso (target i)).hom.toFun
      ((coefficientChart i).hom.toFun z)).val = z.val := by
  cases i with
  | name =>
      exact (NumericalNamed.coefficient_inverse_code (variableIso.inv.toFun z)).trans rfl
  | function k =>
      exact (NumericalNamed.coefficient_inverse_code (C := functions k) z).trans
        (NumericalTuples.code_one z.val)
  | relation k =>
      exact (NumericalNamed.coefficient_inverse_code (C := relations k) z).trans
        (NumericalTuples.code_one z.val)

def term : SyntaxPolynomial Label := SyntaxPolynomial.termExpression .name Label.function bound
def formula : SyntaxPolynomial Label := SyntaxPolynomial.formulaExpression .name Label.relation bound

abbrev sourceTerm : SyntaxPolynomial (PredicateCategory 𝗣𝗔) := SyntaxPolynomial.termExpression variableSymbols functionSymbols bound
abbrev sourceFormula : SyntaxPolynomial (PredicateCategory 𝗣𝗔) := SyntaxPolynomial.formulaExpression variableSymbols relationSymbols bound
abbrev targetTerm : SyntaxPolynomial (PredicateCategory 𝗧𝗔) := SyntaxPolynomial.termExpression (NumericalCoordinates.codedPredicate NumericalNamed.variableObject)
  (LiteralSignature.coefficients functionSymbols) bound
abbrev targetFormula : SyntaxPolynomial (PredicateCategory 𝗧𝗔) := SyntaxPolynomial.formulaExpression (NumericalCoordinates.codedPredicate NumericalNamed.variableObject)
  (LiteralSignature.coefficients relationSymbols) bound

theorem term_source : term.mapCoefficients source = sourceTerm := by
  simp only [term,SyntaxOperationsTransport.mapCoefficients_termExpression,source]
theorem term_target : term.mapCoefficients target = targetTerm := by
  simp only [term,SyntaxOperationsTransport.mapCoefficients_termExpression,target]
theorem formula_source : formula.mapCoefficients source = sourceFormula := by
  simp only [formula,SyntaxOperationsTransport.mapCoefficients_formulaExpression,source]
theorem formula_target : formula.mapCoefficients target = targetFormula := by
  simp only [formula,SyntaxOperationsTransport.mapCoefficients_formulaExpression,target]

def termChart : numericalInterpretation.obj originalSyntax.algebra.a.1 ≅ E.functor.obj sourceSyntax.algebra.a.1 :=
  termIso.symm ≪≫ (NumericalNamed.literalTermIso NumericalNamed.variableObject functions relations bound).symm
def formulaChart : numericalInterpretation.obj originalSyntax.algebra.a.2 ≅ E.functor.obj sourceSyntax.algebra.a.2 :=
  formulaIso.symm ≪≫ (NumericalNamed.literalFormulaIso NumericalNamed.variableObject functions relations bound).symm

theorem term_value (z : Obj 𝗣𝗔 ℕ originalSyntax.algebra.a.1) :
    ((NumericalCoordinates.predicatePresentationIso sourceSyntax.algebra.a.1).hom.toFun
      (termChart.hom.toFun z)).val = z.val := termIso_inverse_value z
theorem formula_value (z : Obj 𝗣𝗔 ℕ originalSyntax.algebra.a.2) :
    ((NumericalCoordinates.predicatePresentationIso sourceSyntax.algebra.a.2).hom.toFun
      (formulaChart.hom.toFun z)).val = z.val := formulaIso_inverse_value z

def termInputIso : numericalInterpretation.obj (sourceTerm.eval.obj originalSyntax.algebra.a) ≅
    E.functor.obj (targetTerm.eval.obj sourceSyntax.algebra.a) :=
  NumericalPolynomialRepresentation.normalizedIso source target coefficientChart originalSyntax.algebra.a.1 originalSyntax.algebra.a.2
    sourceSyntax.algebra.a.1 sourceSyntax.algebra.a.2 termChart formulaChart
    term sourceTerm targetTerm term_source term_target

def formulaInputIso : numericalInterpretation.obj (sourceFormula.eval.obj originalSyntax.algebra.a) ≅
    E.functor.obj (targetFormula.eval.obj sourceSyntax.algebra.a) :=
  NumericalPolynomialRepresentation.normalizedIso source target coefficientChart originalSyntax.algebra.a.1 originalSyntax.algebra.a.2
    sourceSyntax.algebra.a.1 sourceSyntax.algebra.a.2 termChart formulaChart
    formula sourceFormula targetFormula formula_source formula_target

def termInput (z : Obj 𝗣𝗔 ℕ (sourceTerm.eval.obj originalSyntax.algebra.a)) :
    Obj 𝗧𝗔 ℕ (targetTerm.eval.obj sourceSyntax.algebra.a) :=
  (NumericalCoordinates.predicatePresentationIso (targetTerm.eval.obj sourceSyntax.algebra.a)).hom.toFun
    (termInputIso.hom.toFun z)
def formulaInput (z : Obj 𝗣𝗔 ℕ (sourceFormula.eval.obj originalSyntax.algebra.a)) :
    Obj 𝗧𝗔 ℕ (targetFormula.eval.obj sourceSyntax.algebra.a) :=
  (NumericalCoordinates.predicatePresentationIso (targetFormula.eval.obj sourceSyntax.algebra.a)).hom.toFun
    (formulaInputIso.hom.toFun z)

theorem term_representation (u : ℕ) (z : Obj 𝗣𝗔 ℕ (sourceTerm.eval.obj originalSyntax.algebra.a)) :
    (baseRepresentation 𝗣𝗔 originalSyntax.algebra.a.1 originalSyntax.algebra.a.2 sourceTerm).val.Evalb ![u,z.val] ↔
      (baseRepresentation 𝗧𝗔 sourceSyntax.algebra.a.1 sourceSyntax.algebra.a.2 targetTerm).val.Evalb ![u,(termInput z).val] :=
  NumericalPolynomialRepresentation.normalized_baseRepresentation_iff source target coefficientChart
    originalSyntax.algebra.a.1 originalSyntax.algebra.a.2 sourceSyntax.algebra.a.1 sourceSyntax.algebra.a.2
    termChart formulaChart term_value formula_value coefficient_value term sourceTerm targetTerm term_source term_target u z

theorem formula_representation (u : ℕ) (z : Obj 𝗣𝗔 ℕ (sourceFormula.eval.obj originalSyntax.algebra.a)) :
    (baseRepresentation 𝗣𝗔 originalSyntax.algebra.a.1 originalSyntax.algebra.a.2 sourceFormula).val.Evalb ![u,z.val] ↔
      (baseRepresentation 𝗧𝗔 sourceSyntax.algebra.a.1 sourceSyntax.algebra.a.2 targetFormula).val.Evalb ![u,(formulaInput z).val] :=
  NumericalPolynomialRepresentation.normalized_baseRepresentation_iff source target coefficientChart
    originalSyntax.algebra.a.1 originalSyntax.algebra.a.2 sourceSyntax.algebra.a.1 sourceSyntax.algebra.a.2
    termChart formulaChart term_value formula_value coefficient_value formula sourceFormula targetFormula formula_source formula_target u z

/-- The actual arithmetic term constructor square, using the canonical
plain polynomial-input chart and the proved ordered coefficient charts. -/
abbrev term_constructor :=
  NumericalDerivationInterpretation.normalized_plain_term_constructor
    source target coefficientChart term formula sourceTerm sourceFormula targetTerm targetFormula
    term_source formula_source term_target formula_target termChart formulaChart
    term_value formula_value coefficient_value

/-- This is the full formula polynomial, including equality, relation
symbols, negation, implication and the named quantifier branch. -/
abbrev formula_constructor :=
  NumericalDerivationInterpretation.normalized_plain_formula_constructor
    source target coefficientChart term formula sourceTerm sourceFormula targetTerm targetFormula
    term_source formula_source term_target formula_target termChart formulaChart
    term_value formula_value coefficient_value

/-- The actual numerical constructor source follows the full polynomial
comparison through the already constructed literal syntax algebra isomorphism. -/
def numericalTermInputIso : numericalInterpretation.obj (sourceTerm.eval.obj originalSyntax.algebra.a) ≅
    (SyntaxPolynomial.termExpression NumericalNamed.variableObject functions bound).eval.obj numericalSyntax.algebra.a :=
  termInputIso ≪≫ NumericalNamed.termConstructorInputIso E NumericalNamed.variableObject functions relations bound
    sourceSyntax numericalSyntax (NumericalNamed.literalAlgebraIso NumericalNamed.variableObject functions relations bound)

def numericalFormulaInputIso : numericalInterpretation.obj (sourceFormula.eval.obj originalSyntax.algebra.a) ≅
    (SyntaxPolynomial.formulaExpression NumericalNamed.variableObject relations bound).eval.obj numericalSyntax.algebra.a :=
  formulaInputIso ≪≫ NumericalNamed.formulaConstructorInputIso E NumericalNamed.variableObject functions relations bound
    sourceSyntax numericalSyntax (NumericalNamed.literalAlgebraIso NumericalNamed.variableObject functions relations bound)

theorem numerical_term_constructor :
    numericalInterpretation.map originalSyntax.algebra.str.1 ≫ termIso.inv =
      numericalTermInputIso.hom ≫ numericalSyntax.algebra.str.1 := by
  let c := NumericalNamed.literalTermIso NumericalNamed.variableObject functions relations bound
  let d := NumericalNamed.termConstructorInputIso E NumericalNamed.variableObject functions relations bound
    sourceSyntax numericalSyntax (NumericalNamed.literalAlgebraIso NumericalNamed.variableObject functions relations bound)
  have hp : numericalInterpretation.map originalSyntax.algebra.str.1 ≫ termChart.hom =
      termInputIso.hom ≫ E.functor.map sourceSyntax.algebra.str.1 := term_constructor
  have hn : E.functor.map sourceSyntax.algebra.str.1 ≫ c.hom =
      d.hom ≫ numericalSyntax.algebra.str.1 :=
    NumericalNamed.termConstructor_input_square E NumericalNamed.variableObject functions relations bound
      sourceSyntax numericalSyntax (NumericalNamed.literalAlgebraIso NumericalNamed.variableObject functions relations bound)
  have hc : termChart.hom ≫ c.hom = termIso.inv := by
    change (termIso.inv ≫ c.inv) ≫ c.hom = termIso.inv
    rw [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  calc
    _ = (numericalInterpretation.map originalSyntax.algebra.str.1 ≫ termChart.hom) ≫ c.hom :=
      (congrArg (fun f => numericalInterpretation.map originalSyntax.algebra.str.1 ≫ f) hc).symm.trans
        (Category.assoc _ _ _).symm
    _ = (termInputIso.hom ≫ E.functor.map sourceSyntax.algebra.str.1) ≫ c.hom :=
      congrArg (fun f => f ≫ c.hom) hp
    _ = termInputIso.hom ≫ (d.hom ≫ numericalSyntax.algebra.str.1) :=
      (Category.assoc _ _ _).trans (congrArg (fun f => termInputIso.hom ≫ f) hn)
    _ = _ := (Category.assoc termInputIso.hom d.hom numericalSyntax.algebra.str.1).symm

theorem numerical_formula_constructor :
    numericalInterpretation.map originalSyntax.algebra.str.2 ≫ formulaIso.inv =
      numericalFormulaInputIso.hom ≫ numericalSyntax.algebra.str.2 := by
  let c := NumericalNamed.literalFormulaIso NumericalNamed.variableObject functions relations bound
  let d := NumericalNamed.formulaConstructorInputIso E NumericalNamed.variableObject functions relations bound
    sourceSyntax numericalSyntax (NumericalNamed.literalAlgebraIso NumericalNamed.variableObject functions relations bound)
  have hp : numericalInterpretation.map originalSyntax.algebra.str.2 ≫ formulaChart.hom =
      formulaInputIso.hom ≫ E.functor.map sourceSyntax.algebra.str.2 := formula_constructor
  have hn : E.functor.map sourceSyntax.algebra.str.2 ≫ c.hom =
      d.hom ≫ numericalSyntax.algebra.str.2 :=
    NumericalNamed.formulaConstructor_input_square E NumericalNamed.variableObject functions relations bound
      sourceSyntax numericalSyntax (NumericalNamed.literalAlgebraIso NumericalNamed.variableObject functions relations bound)
  have hc : formulaChart.hom ≫ c.hom = formulaIso.inv := by
    change (formulaIso.inv ≫ c.inv) ≫ c.hom = formulaIso.inv
    rw [Category.assoc,Iso.inv_hom_id,Category.comp_id]
  calc
    _ = (numericalInterpretation.map originalSyntax.algebra.str.2 ≫ formulaChart.hom) ≫ c.hom :=
      (congrArg (fun f => numericalInterpretation.map originalSyntax.algebra.str.2 ≫ f) hc).symm.trans
        (Category.assoc _ _ _).symm
    _ = (formulaInputIso.hom ≫ E.functor.map sourceSyntax.algebra.str.2) ≫ c.hom :=
      congrArg (fun f => f ≫ c.hom) hp
    _ = formulaInputIso.hom ≫ (d.hom ≫ numericalSyntax.algebra.str.2) :=
      (Category.assoc _ _ _).trans (congrArg (fun f => formulaInputIso.hom ≫ f) hn)
    _ = _ := (Category.assoc formulaInputIso.hom d.hom numericalSyntax.algebra.str.2).symm

end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.SyntaxTemplate
