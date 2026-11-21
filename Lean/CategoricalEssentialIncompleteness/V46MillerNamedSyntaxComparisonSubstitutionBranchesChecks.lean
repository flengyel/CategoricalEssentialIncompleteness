/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerNamedSyntaxComparisonSubstitutionBranches


/-! # Every nonquantified branch of the named substitution fold -/

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
local notation "jt" => NamedSyntaxComparison.substitutionTermStateIso P V σ π d
local notation "jf" => NamedSyntaxComparison.substitutionFormulaStateIso P V σ π d
example : (F).map (S₀).variableSubstitutionPair ≫ (jt).hom=
    (NamedSyntaxComparison.substitutionVariableInputIso P V σ π d).hom ≫ (S₁).variableSubstitutionPair :=
  NamedSyntaxComparison.map_variableSubstitutionPair P V σ π d
example : (F).map (S₀).functionSubstitutionPair ≫ (jt).hom=
    (NamedSyntaxComparison.substitutionConstructorsInputIso P V σ π d σ).hom ≫ (S₁).functionSubstitutionPair :=
  NamedSyntaxComparison.map_functionSubstitutionPair P V σ π d
example : (F).map (S₀).equalitySubstitutionPair ≫ (jf).hom=
    (NamedSyntaxComparison.substitutionPowerInputIso P V σ π d .term 2).hom ≫ (S₁).equalitySubstitutionPair :=
  NamedSyntaxComparison.map_equalitySubstitutionPair P V σ π d
example : (F).map (S₀).relationSubstitutionPair ≫ (jf).hom=
    (NamedSyntaxComparison.substitutionConstructorsInputIso P V σ π d π).hom ≫ (S₁).relationSubstitutionPair :=
  NamedSyntaxComparison.map_relationSubstitutionPair P V σ π d
example : (F).map (S₀).negationSubstitutionPair ≫ (jf).hom=(jf).hom ≫ (S₁).negationSubstitutionPair :=
  NamedSyntaxComparison.map_negationSubstitutionPair P V σ π d
example : (F).map (S₀).implicationSubstitutionPair ≫ (jf).hom=
    (NamedSyntaxComparison.substitutionPowerInputIso P V σ π d .formula 2).hom ≫ (S₁).implicationSubstitutionPair :=
  NamedSyntaxComparison.map_implicationSubstitutionPair P V σ π d


section GenericSquares
variable {X Y A B : PredicateCategory 𝗣𝗔} {X' Y' A' B' : Total.TotalCategory P}
example (k : (F).obj X ≅ X') (l : (F).obj Y ≅ Y')
    (i : (F).obj A ≅ A') (j : (F).obj B ≅ B')
    (u : X ⟶ A) (v : Y ⟶ B) (u' : X' ⟶ A') (v' : Y' ⟶ B')
    (hu : (F).map u ≫ i.hom = k.hom ≫ u')
    (hv : (F).map v ≫ j.hom = l.hom ≫ v') :
    (F).map (prod.map u v) ≫ (NamedSyntaxComparison.Options.productIso (F) i j).hom =
      (NamedSyntaxComparison.Options.productIso (F) k l).hom ≫ prod.map u' v' :=
  NamedSyntaxComparison.substitution_product_square P k l i j u v u' v' hu hv

example {X X0 : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔}
    {Y Y0 : Total.TotalCategory P × Total.TotalCategory P}
    (c : ((F).prod (F)).obj X ≅ Y) (c0 : ((F).prod (F)).obj X0 ≅ Y0)
    (u : X ⟶ X0) (v : Y ⟶ Y0)
    (hc : ((F).prod (F)).map u ≫ c0.hom = c.hom ≫ v)
    (a : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) (r : SyntaxPolynomial (Total.TotalCategory P))
    (ha : Syntax.Polynomial.mapped P a = r)
    {Z : PredicateCategory 𝗣𝗔} {Z' : Total.TotalCategory P}
    (j : (F).obj Z ≅ Z') (g : a.eval.obj X0 ⟶ Z) (h : r.eval.obj Y0 ⟶ Z')
    (hgh : (F).map g ≫ j.hom =
      (NamedSyntaxComparison.constructorInput P X0 Y0 c0 a r ha).hom ≫ h) :
    (F).map (a.eval.map u ≫ g) ≫ j.hom =
      (NamedSyntaxComparison.constructorInput P X Y c a r ha).hom ≫ r.eval.map v ≫ h :=
  NamedSyntaxComparison.substitution_polynomial_constructor P c c0 u v hc a r ha j g h hgh
end GenericSquares
