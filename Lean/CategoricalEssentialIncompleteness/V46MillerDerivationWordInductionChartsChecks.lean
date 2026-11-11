/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerDerivationWordInductionCharts


/-! # Statement checks in `V46MillerDerivationWordInductionChartsChecks` -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.Miller
variable {P : Uniform.Family} (labels : ℕ → Total.TotalCategory P) (X Y Z : Total.TotalCategory P)
variable (g : Y ⟶ Z) (n : ℕ)
example : Derivation.WordInduction.constructorsData labels X Y n=
    Derivation.WordInduction.constructorsData labels X Z n :=
  Derivation.WordInduction.constructorsData_second labels X Y Z n
example : eqToHom (congrArg Derivation.WordInduction.ChartData.source
    (Derivation.WordInduction.constructorsData_second labels X Y Z n)) ≫
      (Syntax.Raw.baseComparison X Z (SyntaxPolynomial.constructors labels n)).hom=
    (Syntax.Raw.baseComparison X Y (SyntaxPolynomial.constructors labels n)).hom ≫
      (SyntaxPolynomial.constructors labels n).eval.map ((𝟙 X,g) : (X,Y) ⟶ (X,Z)) :=
  Derivation.WordInduction.constructors_raw_square labels X Y Z g n
