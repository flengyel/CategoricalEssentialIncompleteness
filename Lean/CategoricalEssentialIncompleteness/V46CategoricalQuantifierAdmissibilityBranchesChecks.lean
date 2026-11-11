/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalQuantifierAdmissibilityBranches

/-! Actual result maps on both summands of the quantified domain. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D} {σ π : ℕ → D} {d : ℕ} (S : CategoricalSyntax V σ π d)

example : (S.quantifiedDistinctAdmissibility : D) ⟶ S.admissibleSubstitution :=
  S.quantifiedDistinctBody

example : S.quantifiedDistinctBody ≫ S.admissibleInclusion =
    S.quantifiedDistinctAdmissibility.arrow ≫ S.quantifiedBody :=
  S.quantifiedDistinctBody_square

example : S.quantifiedEqualAdmissible ≫ S.admissibleInclusion =
    (Two.fiberSubobject S.quantifiedEquality true).arrow ≫ S.quantifiedInput :=
  S.quantifiedEqualAdmissible_inclusion

example : S.quantifiedEqualAdmissible ≫ S.formulaSubstitution =
    (Two.fiberSubobject S.quantifiedEquality true).arrow ≫
      prod.fst ≫ S.quantifierConstructor := S.quantifiedEqualAdmissible_result

example : S.quantifiedDistinctAdmissible ≫ S.admissibleInclusion =
    S.quantifiedDistinctAdmissibility.arrow ≫ S.quantifiedInput :=
  S.quantifiedDistinctAdmissible_inclusion

example : S.quantifiedDistinctAdmissible ≫ S.formulaSubstitution =
    prod.lift (S.quantifiedDistinctAdmissibility.arrow ≫ prod.fst ≫ prod.fst)
      (S.quantifiedDistinctBody ≫ S.formulaSubstitution) ≫ S.quantifierConstructor :=
  S.quantifiedDistinctAdmissible_result
