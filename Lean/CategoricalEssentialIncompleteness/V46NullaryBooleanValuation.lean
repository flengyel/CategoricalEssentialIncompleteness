/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryLogicalInterpretation
public import CategoricalEssentialIncompleteness.TwoBoolean

/-! # Boolean valuations of the nullary-predicate language

Terms are interpreted in the terminal object, equality has value true,
and quantification is the projection on the formula value.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D}

def implies (a b : Bool) : Bool := !a || b

def algebra (V : D) (d : X ⟶ Two D) : NullarySyntaxAlgebra.Algebra V X where
  a := (⊤_ D, Two D)
  str := (coprod.desc (terminal.from V) (terminal.from ((⊥_ D) ⨯ (⊤_ D))),
    coprod.desc
      (coprod.desc
        (coprod.desc
          (coprod.desc (Two.constant ((⊤_ D) ⨯ (⊤_ D)) true) (prod.fst ≫ d))
          (Two.unary Bool.not (𝟙 (Two D))))
        (Two.binaryArrow implies))
      prod.snd)

variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0)
variable (d : X ⟶ Two D)

def valuation : S.algebra.a.2 ⟶ Two D := (S.fold (algebra V d)).2

@[reassoc] theorem equality_value :
    S.equalityConstructor ≫ valuation S d = Two.constant (S.algebra.a.1 ⨯ S.algebra.a.1) true := by
  have h := congrArg Prod.snd (S.fold_commutes (algebra V d))
  have hh := congrArg (fun k => (coprod.inl ≫ coprod.inl ≫ coprod.inl ≫ coprod.inl) ≫ k) h
  simpa [valuation, algebra, CategoricalSyntax.equalityConstructor,
    SyntaxPolynomial.jointFunctor, SyntaxPolynomial.formulaExpression,
    SyntaxPolynomial.power, SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor,
    SyntaxPolynomial.productFunctor, Category.assoc] using hh.symm

@[reassoc] theorem atom_value :
    NullaryInterpretation.atomFormula S ≫ valuation S d = d := by
  have h := congrArg Prod.snd (S.fold_commutes (algebra V d))
  have hh := congrArg (fun k =>
    (prod.lift (𝟙 X) (terminal.from X) ≫ coprod.inr ≫
      coprod.inl ≫ coprod.inl ≫ coprod.inl) ≫ k) h
  simpa [valuation, algebra, NullaryInterpretation.atomFormula,
    CategoricalSyntax.relationConstructors, SyntaxPolynomial.jointFunctor,
    SyntaxPolynomial.formulaExpression, SyntaxPolynomial.constructors,
    SyntaxPolynomial.power, SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor,
    SyntaxPolynomial.productFunctor, Category.assoc] using hh.symm

@[reassoc] theorem negation_value :
    S.negationConstructor ≫ valuation S d = Two.unary Bool.not (valuation S d) := by
  have h := congrArg Prod.snd (S.fold_commutes (algebra V d))
  have hh := congrArg (fun k => (coprod.inr ≫ coprod.inl ≫ coprod.inl) ≫ k) h
  simpa [valuation, algebra, CategoricalSyntax.negationConstructor,
    CategoricalSyntax.negationInjection, SyntaxPolynomial.jointFunctor,
    SyntaxPolynomial.formulaExpression, SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor,
    SyntaxPolynomial.productFunctor, Category.assoc] using hh.symm

@[reassoc] theorem implication_value :
    S.implicationConstructor ≫ valuation S d =
      Two.binary implies (prod.fst ≫ valuation S d) (prod.snd ≫ valuation S d) := by
  have h := congrArg Prod.snd (S.fold_commutes (algebra V d))
  have hh := congrArg (fun k => (coprod.inr ≫ coprod.inl) ≫ k) h
  simpa [valuation, algebra, CategoricalSyntax.implicationConstructor,
    SyntaxPolynomial.jointFunctor, SyntaxPolynomial.formulaExpression,
    SyntaxPolynomial.power, SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor,
    SyntaxPolynomial.productFunctor, Category.assoc, Two.binary] using hh.symm

@[reassoc] theorem quantifier_value :
    S.quantifierConstructor ≫ valuation S d = prod.snd ≫ valuation S d := by
  have h := congrArg Prod.snd (S.fold_commutes (algebra V d))
  have hh := congrArg (fun k => coprod.inr ≫ k) h
  simpa [valuation, algebra, CategoricalSyntax.quantifierConstructor,
    SyntaxPolynomial.jointFunctor, SyntaxPolynomial.formulaExpression,
    SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor,
    Category.assoc] using hh.symm

end CategoricalEssentialIncompleteness.V46.NullaryBooleanValuation
