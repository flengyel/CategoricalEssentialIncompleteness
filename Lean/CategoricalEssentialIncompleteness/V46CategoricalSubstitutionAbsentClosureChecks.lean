/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionAbsentClosure

/-! Closure is proved for the mutual syntax polynomial and substitution algebra. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D} {σ π : ℕ → D} {d : ℕ} (S : CategoricalSyntax V σ π d)

example {A : Over S.substitutionParameters × Over S.substitutionParameters}
    (m : A ⟶ S.substitutionAlgebra.a) (hm : m ≫ S.absenceMask = m ≫ S.absenceResult) :
    ((SyntaxPolynomial.jointFunctor
      ((SyntaxPolynomial.termExpression V σ d).withParameters S.substitutionParameters)
      ((SyntaxPolynomial.formulaExpression V π d).withParameters S.substitutionParameters)).map m ≫
        S.substitutionAlgebra.str) ≫ S.absenceMask =
      ((SyntaxPolynomial.jointFunctor
        ((SyntaxPolynomial.termExpression V σ d).withParameters S.substitutionParameters)
        ((SyntaxPolynomial.formulaExpression V π d).withParameters S.substitutionParameters)).map m ≫
          S.substitutionAlgebra.str) ≫ S.absenceResult := S.absence_constructor_closed m hm
