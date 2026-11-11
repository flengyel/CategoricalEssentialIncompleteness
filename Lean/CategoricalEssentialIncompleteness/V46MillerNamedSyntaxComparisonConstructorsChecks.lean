/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxComparisonConstructors


/-! # Statement checks in `V46MillerNamedSyntaxComparisonConstructorsChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.Miller
variable (P : Uniform.Family) (V : PredicateCategory 𝗣𝗔) (σ π : ℕ → PredicateCategory 𝗣𝗔) (d : ℕ)
local notation "F" => Syntax.predicateFunctor P
local notation "S₀" => NamedSyntaxComparison.sourceSyntax V σ π d
local notation "S₁" => NamedSyntaxComparison.presentedSyntax P V σ π d
local notation "t" => Iso.symm (NamedSyntaxComparison.termIso P V σ π d)
local notation "f" => Iso.symm (NamedSyntaxComparison.formulaIso P V σ π d)
example : (F).map (S₀).variableConstructor ≫ (t).hom=(S₁).variableConstructor :=
  NamedSyntaxComparison.variable_constructor P V σ π d
example : (F).map (S₀).functionConstructors ≫ (t).hom=
    (NamedSyntaxComparison.functionInput P V σ π d).hom ≫ (S₁).functionConstructors :=
  NamedSyntaxComparison.function_constructors P V σ π d
example : (F).map (S₀).relationConstructors ≫ (f).hom=
    (NamedSyntaxComparison.relationInput P V σ π d).hom ≫ (S₁).relationConstructors :=
  NamedSyntaxComparison.relation_constructors P V σ π d
example : (F).map (S₀).equalityConstructor ≫ (f).hom=
    (NamedSyntaxComparison.Options.productIso (F) (t) (t)).hom ≫ (S₁).equalityConstructor :=
  NamedSyntaxComparison.equality_constructor P V σ π d
example : (F).map (S₀).negationConstructor ≫ (f).hom=(f).hom ≫ (S₁).negationConstructor :=
  NamedSyntaxComparison.negation_constructor P V σ π d
example : (F).map (S₀).implicationConstructor ≫ (f).hom=
    (NamedSyntaxComparison.Options.productIso (F) (f) (f)).hom ≫ (S₁).implicationConstructor :=
  NamedSyntaxComparison.implication_constructor P V σ π d
example : (F).map (S₀).quantifierConstructor ≫ (f).hom=
    (NamedSyntaxComparison.Options.productIso (F) (Iso.refl ((F).obj V)) (f)).hom ≫
      (S₁).quantifierConstructor :=
  NamedSyntaxComparison.quantifier_constructor P V σ π d

-- Both complete structure squares use the actual constructed carrier chart.
example : (F).map (S₀).algebra.str.1 ≫ (t).hom =
    (NamedSyntaxComparison.termInput P V σ π d).hom ≫ (S₁).algebra.str.1 :=
  NamedSyntaxComparison.term_structure P V σ π d
example : (F).map (S₀).algebra.str.2 ≫ (f).hom =
    (NamedSyntaxComparison.formulaInput P V σ π d).hom ≫ (S₁).algebra.str.2 :=
  NamedSyntaxComparison.formula_structure P V σ π d

section GenericInputs
variable (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔)
  (Y : Total.TotalCategory P × Total.TotalCategory P)
  (c : ((Syntax.predicateFunctor P).prod (Syntax.predicateFunctor P)).obj X ≅ Y)
  (a b : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
  (r s : SyntaxPolynomial (Total.TotalCategory P))
  (ha : Syntax.Polynomial.mapped P a = r) (hb : Syntax.Polynomial.mapped P b = s)
example : (F).map (coprod.inl : a.eval.obj X ⟶ a.eval.obj X ⨿ b.eval.obj X) ≫
    (NamedSyntaxComparison.constructorInput P X Y c (.sum a b) (.sum r s)
      (congrArg₂ SyntaxPolynomial.sum ha hb)).hom =
    (NamedSyntaxComparison.constructorInput P X Y c a r ha).hom ≫
      (coprod.inl : r.eval.obj Y ⟶ r.eval.obj Y ⨿ s.eval.obj Y) :=
  by
    simpa only [NamedSyntaxComparison.polynomialInl] using
      NamedSyntaxComparison.constructorInput_inl P X Y c a b r s ha hb
example : (F).map (coprod.inr : b.eval.obj X ⟶ a.eval.obj X ⨿ b.eval.obj X) ≫
    (NamedSyntaxComparison.constructorInput P X Y c (.sum a b) (.sum r s)
      (congrArg₂ SyntaxPolynomial.sum ha hb)).hom =
    (NamedSyntaxComparison.constructorInput P X Y c b s hb).hom ≫
      (coprod.inr : s.eval.obj Y ⟶ r.eval.obj Y ⨿ s.eval.obj Y) :=
  by
    simpa only [NamedSyntaxComparison.polynomialInr] using
      NamedSyntaxComparison.constructorInput_inr P X Y c a b r s ha hb

-- These identify the factored arrows with the original chosen coproduct
-- injections independently, on both sides of the actual uniform functor.
example : NamedSyntaxComparison.polynomialInl (C := PredicateCategory 𝗣𝗔) a b X =
    (coprod.inl : a.eval.obj X ⟶ a.eval.obj X ⨿ b.eval.obj X) :=
  NamedSyntaxComparison.polynomialInl_eq a b X
example : NamedSyntaxComparison.polynomialInr (C := PredicateCategory 𝗣𝗔) a b X =
    (coprod.inr : b.eval.obj X ⟶ a.eval.obj X ⨿ b.eval.obj X) :=
  NamedSyntaxComparison.polynomialInr_eq a b X
example : NamedSyntaxComparison.polynomialInl (C := Total.TotalCategory P) r s Y =
    (coprod.inl : r.eval.obj Y ⟶ r.eval.obj Y ⨿ s.eval.obj Y) :=
  NamedSyntaxComparison.polynomialInl_eq r s Y
example : NamedSyntaxComparison.polynomialInr (C := Total.TotalCategory P) r s Y =
    (coprod.inr : s.eval.obj Y ⟶ r.eval.obj Y ⨿ s.eval.obj Y) :=
  NamedSyntaxComparison.polynomialInr_eq r s Y
end GenericInputs
