/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionIdentity

/-! Identity substitution retains the original named variable and arbitrary syntax. -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D} {σ π : ℕ → D} {d : ℕ} (S : CategoricalSyntax V σ π d)

example : S.identityParameters = prod.lift (𝟙 V) S.variableConstructor := rfl

example : S.algebra.a.1 ⨯ V ⟶ S.algebra.a.1 ⨯ S.substitutionParameters :=
  S.identityTermInput

example : S.identityTermInput ≫ S.termSubstitution = prod.fst :=
  S.term_substitution_identity

example : S.identityFormulaInput ≫ S.formulaSubstitutionOption = prod.fst ≫ coprod.inr :=
  S.formula_substitution_identity

example : S.algebra.a.2 ⨯ V ⟶ S.admissibleSubstitution := S.identityFormulaAdmissible

example : S.identityFormulaAdmissible ≫ S.admissibleInclusion = S.identityFormulaInput :=
  S.identityFormulaAdmissible_inclusion

example : S.identityFormulaAdmissible ≫ S.formulaSubstitution = prod.fst :=
  S.identityFormulaAdmissible_substitution

example {X : D} (t : X ⟶ S.algebra.a.1) (x : X ⟶ V) :
    prod.lift t x ≫ S.identityTermInput ≫ S.termSubstitution = t := by
  rw [S.term_substitution_identity, prod.lift_fst]

example {X : D} (φ : X ⟶ S.algebra.a.2) (x : X ⟶ V) :
    prod.lift φ x ≫ S.identityFormulaInput ≫ S.formulaSubstitutionOption = φ ≫ coprod.inr := by
  rw [S.formula_substitution_identity, prod.lift_fst_assoc]
