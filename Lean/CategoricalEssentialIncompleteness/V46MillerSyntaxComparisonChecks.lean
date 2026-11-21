/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxComparison


/-! # The original syntax polynomial under the ordinary word inclusion -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax.Checks
example (P : Uniform.Family) : PreservesFiniteLimits (predicateFunctor P) := inferInstance
example (P : Uniform.Family) : PreservesFiniteCoproducts (predicateFunctor P) := inferInstance
example (P : Uniform.Family) (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) :
    p.eval ⋙ predicateFunctor P ≅
      ((predicateFunctor P).prod (predicateFunctor P)) ⋙ (Polynomial.mapped P p).eval :=
  Polynomial.naturalIso P p
noncomputable example (P : Uniform.Family) (p q : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) :
    Endofunctor.Algebra (SyntaxPolynomial.jointFunctor (Polynomial.mapped P p) (Polynomial.mapped P q)) :=
  Polynomial.wordAlgebra P p q
end CategoricalEssentialIncompleteness.V46.Miller.Syntax.Checks
