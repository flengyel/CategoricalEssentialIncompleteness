/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionIdentity

/-! # The variable equation of named substitution -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.CategoricalSyntax

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D} {σ π : ℕ → D} {d : ℕ} (S : CategoricalSyntax V σ π d)

theorem variable_fold_in_slice :
    (constantFamilyFunctor S.substitutionParameters).map S.variableConstructor ≫
        S.substitutionFold.1 = parameterHom S.variableSubstitutionPair := by
  have h := congrArg Prod.fst S.substitutionFold_commutes
  change ((SyntaxPolynomial.termExpression V σ d).withParameters
      S.substitutionParameters).eval.map S.substitutionFold ≫ S.substitutionAlgebra.str.1 =
    (SyntaxPolynomial.algebraWithParameters (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d) S.algebra S.substitutionParameters).str.1 ≫
        S.substitutionFold.1 at h
  rw [S.term_parameter_structure S.substitutionParameters] at h
  let j : constantFamily S.substitutionParameters V ⟶
      ((SyntaxPolynomial.termExpression V σ d).withParameters
        S.substitutionParameters).eval.obj
        (constantFamily S.substitutionParameters S.algebra.a.1,
          constantFamily S.substitutionParameters S.algebra.a.2) := coprod.inl
  have hh := congrArg (fun k => j ≫ k) h
  simpa only [j, SyntaxPolynomial.termExpression, SyntaxPolynomial.withParameters,
    SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor, CategoryTheory.Functor.const,
    substitutionAlgebra, coprod.inl_map_assoc, coprod.inl_desc, coprod.inl_desc_assoc,
    Category.id_comp, Category.assoc] using hh.symm

theorem variable_fold_value :
    prod.map (𝟙 S.substitutionParameters) S.variableConstructor ≫
        S.substitutionFold.1.left ≫ prod.snd = S.variableSubstitutionPair := by
  have h := congrArg (fun k => k.left ≫ prod.snd) S.variable_fold_in_slice
  simpa only [constantFamilyFunctor, Over.comp_left, Over.homMk_left,
    parameterHom, Category.assoc, prod.lift_snd] using h

theorem variable_substitution_value {Z : D} (p : Z ⟶ S.substitutionParameters) (y : Z ⟶ V) :
    prod.lift (y ≫ S.variableConstructor) p ≫ S.termSubstitution =
      prod.lift p y ≫ S.variableSubstitutionPair ≫ prod.snd := by
  have hb : prod.lift (y ≫ S.variableConstructor) p ≫
      (prod.braiding S.algebra.a.1 S.substitutionParameters).hom =
      prod.lift p y ≫ prod.map (𝟙 S.substitutionParameters) S.variableConstructor := by
    apply prod.hom_ext <;> simp [prod.braiding_hom]
  unfold termSubstitution
  rw [← Category.assoc, hb]
  have h := congrArg (fun k => prod.lift p y ≫ k ≫ prod.snd) S.variable_fold_value
  simpa only [Category.assoc] using h

theorem variable_substitution {Z : D} (p : Z ⟶ S.substitutionParameters) (y : Z ⟶ V) :
    prod.lift (y ≫ S.variableConstructor) p ≫ S.termSubstitution =
      Two.branch (prod.lift y (p ≫ prod.fst) ≫ S.decidableVariables.test)
        (y ≫ S.variableConstructor) (p ≫ prod.snd) := by
  rw [S.variable_substitution_value]
  simp only [variableSubstitutionPair, prod.lift_snd_assoc, branch_natural,
    prod.comp_lift_assoc, prod.lift_snd, prod.lift_fst_assoc]

end CategoricalEssentialIncompleteness.V46.CategoricalSyntax
