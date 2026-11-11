/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullaryFormulaSubstitution

/-! # Statement checks for NullaryFormulaSubstitution -/

@[expose] public section

noncomputable section

universe v u
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D}
variable (S : CategoricalSyntax V (fun _ => ⊥_ D) (fun _ => X) 0)
variable {σ π : ℕ → D} {d : ℕ} (Q : CategoricalSyntax V σ π d)
variable (f : X ⟶ Q.sentenceObject)
open NullaryInterpretation

example :
    S.substitutionFold ≫ (substitutionComparisonHom S Q f).f =
      (interpretedSubstitutionHom S Q f).f := NullaryInterpretation.substitution_fold_comparison S Q f

#print axioms CategoricalEssentialIncompleteness.V46.NullaryInterpretation.substitution_fold_comparison

example :
    S.formulaSubstitutionOption ≫ OptionSyntax.map (interpretation S Q f).2 =
      prod.map (interpretation S Q f).2 (substitutionParameterMap S Q f) ≫
        Q.formulaSubstitutionOption := NullaryInterpretation.formula_substitution_option S Q f

#print axioms CategoricalEssentialIncompleteness.V46.NullaryInterpretation.formula_substitution_option

example :
    admissibleInterpretation S Q f ≫ Q.admissibleInclusion =
      S.admissibleInclusion ≫
        prod.map (interpretation S Q f).2 (substitutionParameterMap S Q f) := NullaryInterpretation.admissibleInterpretation_inclusion S Q f

#print axioms CategoricalEssentialIncompleteness.V46.NullaryInterpretation.admissibleInterpretation_inclusion

example :
    admissibleInterpretation S Q f ≫ Q.formulaSubstitution =
      S.formulaSubstitution ≫ (interpretation S Q f).2 := NullaryInterpretation.admissibleInterpretation_result S Q f

#print axioms CategoricalEssentialIncompleteness.V46.NullaryInterpretation.admissibleInterpretation_result
