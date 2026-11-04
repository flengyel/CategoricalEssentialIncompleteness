/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46CategoricalSubstitution
import CategoricalEssentialIncompleteness.V46CategoricalDeletionLaws

/-! # Constructor equations for named free-variable occurrence lists -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.CategoricalSyntax

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V : D} {σ π : ℕ → D} {d : ℕ} (S : CategoricalSyntax V σ π d)

theorem variable_occurrences :
    S.variableConstructor ≫ S.termOccurrences = S.lists.singleton := by
  have h := congrArg Prod.fst (S.fold_commutes S.occurrenceAlgebra)
  have hh := congrArg (fun k => coprod.inl ≫ k) h
  simpa [SyntaxPolynomial.jointFunctor, SyntaxPolynomial.termExpression,
    SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor,
    occurrenceAlgebra, variableConstructor, termOccurrences, formulaOccurrences,
    coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc, coprod.inr_desc_assoc,
    Category.assoc] using hh.symm

theorem variable_membership {X : D} (x y : X ⟶ V) :
    prod.lift x (y ≫ S.variableConstructor ≫ S.termOccurrences) ≫
        S.lists.membership S.decidableVariables =
      prod.lift x y ≫ S.decidableVariables.test := by
  rw [S.variable_occurrences]
  simp only [StableListAlgebra.singleton, prod.comp_lift, Category.comp_id,
    ← Category.assoc, terminal.comp_from]
  rw [S.lists.membership_cons_general, S.lists.membership_nil_general]
  exact sup_bot_eq _

theorem function_occurrences :
    S.functionConstructors ≫ S.termOccurrences =
      (SyntaxPolynomial.constructors σ d).eval.map (S.termOccurrences, S.formulaOccurrences) ≫
        S.lists.constructorOccurrences σ d := by
  have h := congrArg Prod.fst (S.fold_commutes S.occurrenceAlgebra)
  have hh := congrArg (fun k => coprod.inr ≫ k) h
  simpa [SyntaxPolynomial.jointFunctor, SyntaxPolynomial.termExpression,
    SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor,
    occurrenceAlgebra, functionConstructors, termOccurrences, formulaOccurrences,
    coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc, coprod.inr_desc_assoc,
    Category.assoc] using hh.symm

theorem equality_occurrences :
    S.equalityConstructor ≫ S.formulaOccurrences =
      prod.map S.termOccurrences S.termOccurrences ≫ S.lists.append := by
  have h := congrArg Prod.snd (S.fold_commutes S.occurrenceAlgebra)
  have hh := congrArg (fun k => (coprod.inl ≫ coprod.inl ≫ coprod.inl ≫ coprod.inl) ≫ k) h
  simpa [SyntaxPolynomial.jointFunctor, SyntaxPolynomial.formulaExpression,
    SyntaxPolynomial.power, SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor,
    SyntaxPolynomial.productFunctor, occurrenceAlgebra, equalityConstructor,
    termOccurrences, formulaOccurrences, coprod.inl_desc, coprod.inr_desc,
    coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.assoc] using hh.symm

theorem relation_occurrences :
    S.relationConstructors ≫ S.formulaOccurrences =
      (SyntaxPolynomial.constructors π d).eval.map (S.termOccurrences, S.formulaOccurrences) ≫
        S.lists.constructorOccurrences π d := by
  have h := congrArg Prod.snd (S.fold_commutes S.occurrenceAlgebra)
  have hh := congrArg (fun k => (coprod.inr ≫ coprod.inl ≫ coprod.inl ≫ coprod.inl) ≫ k) h
  simpa [SyntaxPolynomial.jointFunctor, SyntaxPolynomial.formulaExpression,
    SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor,
    occurrenceAlgebra, relationConstructors, termOccurrences, formulaOccurrences,
    coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc, coprod.inr_desc_assoc,
    Category.assoc] using hh.symm

theorem implication_occurrences :
    S.implicationConstructor ≫ S.formulaOccurrences =
      prod.map S.formulaOccurrences S.formulaOccurrences ≫ S.lists.append := by
  have h := congrArg Prod.snd (S.fold_commutes S.occurrenceAlgebra)
  have hh := congrArg (fun k => (coprod.inr ≫ coprod.inl) ≫ k) h
  simpa [SyntaxPolynomial.jointFunctor, SyntaxPolynomial.formulaExpression,
    SyntaxPolynomial.power, SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor,
    SyntaxPolynomial.productFunctor, occurrenceAlgebra, implicationConstructor,
    termOccurrences, formulaOccurrences, coprod.inl_desc, coprod.inr_desc,
    coprod.inl_desc_assoc, coprod.inr_desc_assoc, Category.assoc] using hh.symm

theorem quantifier_occurrences :
    S.quantifierConstructor ≫ S.formulaOccurrences =
      prod.map (𝟙 V) S.formulaOccurrences ≫ S.lists.deletion S.decidableVariables := by
  have h := congrArg Prod.snd (S.fold_commutes S.occurrenceAlgebra)
  have hh := congrArg (fun k => coprod.inr ≫ k) h
  simpa [SyntaxPolynomial.jointFunctor, SyntaxPolynomial.formulaExpression,
    SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor,
    occurrenceAlgebra, quantifierConstructor, termOccurrences, formulaOccurrences,
    coprod.inl_desc, coprod.inr_desc, coprod.inl_desc_assoc, coprod.inr_desc_assoc,
    Category.assoc] using hh.symm

/-- Quantification deletes exactly the occurrences of its bound name. -/
theorem quantifier_membership {X : D} (x y : X ⟶ V) (φ : X ⟶ S.algebra.a.2) :
    prod.lift x (prod.lift y φ ≫ S.quantifierConstructor ≫ S.formulaOccurrences) ≫
        S.lists.membership S.decidableVariables =
      Two.binary Bool.and (Two.unary Bool.not (prod.lift x y ≫ S.decidableVariables.test))
        (prod.lift x (φ ≫ S.formulaOccurrences) ≫ S.lists.membership S.decidableVariables) := by
  rw [S.quantifier_occurrences]
  simpa only [← Category.assoc, prod.lift_map, Category.comp_id] using
    S.lists.membership_deletion S.decidableVariables x y (φ ≫ S.formulaOccurrences)

theorem quantifier_bound_name_absent {X : D} (y : X ⟶ V) (φ : X ⟶ S.algebra.a.2) :
    prod.lift y (prod.lift y φ ≫ S.quantifierConstructor ≫ S.formulaOccurrences) ≫
        S.lists.membership S.decidableVariables = Two.constant X false := by
  rw [S.quantifier_membership,
    (S.decidableVariables.test_true_iff y y).mpr rfl, Two.unary_constant]
  exact bot_inf_eq _

end CategoricalEssentialIncompleteness.V46.CategoricalSyntax
