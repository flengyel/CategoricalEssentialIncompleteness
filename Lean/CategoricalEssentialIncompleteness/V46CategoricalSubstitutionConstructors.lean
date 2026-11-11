/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalVariableSubstitution
public import CategoricalEssentialIncompleteness.V46SliceProductCoordinates

/-! # Constructor equations of the substitution fold in its parameter slice -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.CategoricalSyntax

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D} {σ π : ℕ → D} {d : ℕ} (S : CategoricalSyntax V σ π d)

theorem equality_fold_in_slice :
    constantProductComparison S.substitutionParameters S.algebra.a.1 S.algebra.a.1 ≫
        (constantFamilyFunctor S.substitutionParameters).map S.equalityConstructor ≫
        S.substitutionFold.2 =
      prod.map S.substitutionFold.1 S.substitutionFold.1 ≫
        constantProductComparison S.substitutionParameters
          S.substitutionCarriers.1 S.substitutionCarriers.1 ≫
        (constantFamilyFunctor S.substitutionParameters).map S.equalitySubstitutionPair := by
  have h := congrArg Prod.snd S.substitutionFold_commutes
  change (((SyntaxPolynomial.formulaExpression V π d).withParameters
      S.substitutionParameters).eval.map S.substitutionFold) ≫ S.substitutionAlgebra.str.2 =
    (SyntaxPolynomial.algebraWithParameters (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d) S.algebra S.substitutionParameters).str.2 ≫
        S.substitutionFold.2 at h
  rw [S.formula_parameter_structure S.substitutionParameters] at h
  have hh := congrArg (fun k => (coprod.inl ≫ coprod.inl ≫ coprod.inl ≫ coprod.inl) ≫ k) h
  simpa [SyntaxPolynomial.formulaExpression, SyntaxPolynomial.withParameters,
    SyntaxPolynomial.power, SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor,
    SyntaxPolynomial.productFunctor, SyntaxPolynomial.parameterComparison,
    substitutionAlgebra, Category.assoc, coprod.inl_desc, coprod.inl_desc_assoc] using hh.symm

theorem negation_fold_in_slice :
    (constantFamilyFunctor S.substitutionParameters).map S.negationConstructor ≫
        S.substitutionFold.2 =
      S.substitutionFold.2 ≫
        (constantFamilyFunctor S.substitutionParameters).map S.negationSubstitutionPair := by
  have h := congrArg Prod.snd S.substitutionFold_commutes
  change (((SyntaxPolynomial.formulaExpression V π d).withParameters
      S.substitutionParameters).eval.map S.substitutionFold) ≫ S.substitutionAlgebra.str.2 =
    (SyntaxPolynomial.algebraWithParameters (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d) S.algebra S.substitutionParameters).str.2 ≫
        S.substitutionFold.2 at h
  rw [S.formula_parameter_structure S.substitutionParameters] at h
  have hh := congrArg (fun k => (coprod.inr ≫ coprod.inl ≫ coprod.inl) ≫ k) h
  simpa [SyntaxPolynomial.formulaExpression, SyntaxPolynomial.withParameters,
    SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor,
    substitutionAlgebra, Category.assoc, coprod.inl_desc, coprod.inl_desc_assoc,
    coprod.inr_desc, coprod.inr_desc_assoc] using hh.symm

theorem implication_fold_in_slice :
    constantProductComparison S.substitutionParameters S.algebra.a.2 S.algebra.a.2 ≫
        (constantFamilyFunctor S.substitutionParameters).map S.implicationConstructor ≫
        S.substitutionFold.2 =
      prod.map S.substitutionFold.2 S.substitutionFold.2 ≫
        constantProductComparison S.substitutionParameters
          S.substitutionCarriers.2 S.substitutionCarriers.2 ≫
        (constantFamilyFunctor S.substitutionParameters).map S.implicationSubstitutionPair := by
  have h := congrArg Prod.snd S.substitutionFold_commutes
  change (((SyntaxPolynomial.formulaExpression V π d).withParameters
      S.substitutionParameters).eval.map S.substitutionFold) ≫ S.substitutionAlgebra.str.2 =
    (SyntaxPolynomial.algebraWithParameters (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d) S.algebra S.substitutionParameters).str.2 ≫
        S.substitutionFold.2 at h
  rw [S.formula_parameter_structure S.substitutionParameters] at h
  have hh := congrArg (fun k => (coprod.inr ≫ coprod.inl) ≫ k) h
  simpa [SyntaxPolynomial.formulaExpression, SyntaxPolynomial.withParameters,
    SyntaxPolynomial.power, SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor,
    SyntaxPolynomial.productFunctor, SyntaxPolynomial.parameterComparison,
    substitutionAlgebra, Category.assoc, coprod.inl_desc, coprod.inl_desc_assoc,
    coprod.inr_desc, coprod.inr_desc_assoc] using hh.symm

end CategoricalEssentialIncompleteness.V46.CategoricalSyntax
