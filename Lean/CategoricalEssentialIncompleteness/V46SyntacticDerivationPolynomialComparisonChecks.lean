/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticDerivationPolynomialComparison


/-! # Finite rule coproducts and the ordered constructor polynomial -/

@[expose] public section
noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SyntacticDerivation.PolynomialComparisonChecks
variable {D : Type u} [Category.{v} D] [Regular D] [HasFiniteCoproducts D]
open PolynomialComparison
example {F : D} {N : ℕ} (R : RulePresentation F N) :
    nested (coefficients R) N ≅ ordinary R := comparison R
example (σ : ℕ → D) (X : D) (N : ℕ) (i : Fin (N + 1)) :
    injection σ X N i ≫ (component σ N X).hom =
      Sigma.ι (fun j : Fin (N + 1) => σ j.val ⨯ finitePower X j.val) i :=
  injection_component σ N X i
example {F : D} {N : ℕ} (R : RulePresentation F N)
    (A : Endofunctor.Algebra (nested (coefficients R) N)) (hA : IsInitial A) :
    IsInitial (mappedAlgebra R A) := mappedInitial R A hA
end CategoricalEssentialIncompleteness.V46.SyntacticDerivation.PolynomialComparisonChecks
