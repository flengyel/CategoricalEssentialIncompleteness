/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NullarySubstitutionCapture

/-! # Statement checks for NullarySubstitutionCapture -/

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

example {W : D} (x : W ⟶ V) (a : W ⟶ S.algebra.a.2) :
    prod.lift x (a ≫ (interpretation S Q f).2 ≫ Q.formulaOccurrences) ≫
        Q.lists.membership Q.decidableVariables =
      prod.lift x (a ≫ S.formulaOccurrences) ≫ S.lists.membership S.decidableVariables := NullaryInterpretation.formula_membership S Q f x a

#print axioms CategoricalEssentialIncompleteness.V46.NullaryInterpretation.formula_membership

example {W : D} (x : W ⟶ V) (a : W ⟶ S.algebra.a.1) :
    prod.lift x (a ≫ (interpretation S Q f).1 ≫ Q.termOccurrences) ≫
        Q.lists.membership Q.decidableVariables =
      prod.lift x (a ≫ S.termOccurrences) ≫ S.lists.membership S.decidableVariables := NullaryInterpretation.term_membership S Q f x a

#print axioms CategoricalEssentialIncompleteness.V46.NullaryInterpretation.term_membership

example :
    quantifierInputMap S Q f ≫ Q.quantifierEquality = S.quantifierEquality := NullaryInterpretation.quantifier_equality_comparison S Q f

#print axioms CategoricalEssentialIncompleteness.V46.NullaryInterpretation.quantifier_equality_comparison

example : quantifierInputMap S Q f ≫ Q.captureAllowed = S.captureAllowed := NullaryInterpretation.capture_comparison S Q f

#print axioms CategoricalEssentialIncompleteness.V46.NullaryInterpretation.capture_comparison
