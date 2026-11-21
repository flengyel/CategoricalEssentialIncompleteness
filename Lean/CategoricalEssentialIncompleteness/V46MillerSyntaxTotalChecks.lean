/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxTotal


/-! # The concrete syntax bundle in the Miller total splitting -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax
variable {P : Uniform.Family}

example (V : Total.TotalCategory P) (σ π : ℕ → Total.TotalCategory P) (d : ℕ) :
    CategoricalSyntax V σ π d := categoricalSyntax V σ π d

example (z : Point) (V : Total.CanonicalTotal z) (σ π : ℕ → Total.CanonicalTotal z) (d : ℕ) :
    CategoricalSyntax V σ π d := canonicalCategoricalSyntax z V σ π d

example (z : Point) (V : Total.CanonicalTotal z) (σ π : ℕ → Total.CanonicalTotal z)
    (d : ℕ) (R : Total.CanonicalTotal z) :
    IsInitial (SyntaxPolynomial.algebraWithParameters
      (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)
      (canonicalCategoricalSyntax z V σ π d).algebra R) :=
  (canonicalCategoricalSyntax z V σ π d).stable R

end CategoricalEssentialIncompleteness.V46.Miller.Syntax
