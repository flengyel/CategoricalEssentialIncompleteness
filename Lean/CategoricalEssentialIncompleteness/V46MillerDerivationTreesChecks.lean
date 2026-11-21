/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerDerivationTrees


/-! # Ordinary rule-labelled tree algebra with uniform coefficients -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
variable {P : Uniform.Family} {F : Total.TotalCategory P} {N : ℕ} (R : RulePresentation F N)
example : (Derivation.ordinaryTree R).a=
    Syntax.Raw.wordObject false (Derivation.treePolynomial R) .unit := Derivation.ordinaryTree_carrier R
example : (Derivation.ordinaryInputIso R).hom ≫ (Derivation.ordinaryTree R).str=
    Syntax.Raw.rawWordConstructor (Derivation.treePolynomial R) .unit false :=
  Derivation.ordinaryInputIso_constructor R
example (i : Fin (N+1)) :
    SyntacticDerivation.PolynomialComparison.injection (SyntacticDerivation.PolynomialComparison.coefficients R)
      (Derivation.ordinaryTree R).a N i ≫
      (SyntacticDerivation.PolynomialComparison.comparison R).hom.app (Derivation.ordinaryTree R).a ≫
        (Derivation.ordinaryTree R).str=
      prod.map (eqToHom (SyntacticDerivation.PolynomialComparison.coefficients_fin R i)) (𝟙 _) ≫
        Derivation.branchConstructor R i := Derivation.branch_label R i
