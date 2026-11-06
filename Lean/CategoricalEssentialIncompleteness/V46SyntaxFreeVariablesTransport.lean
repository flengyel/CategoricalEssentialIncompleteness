/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntaxFreeVariablesTransportLists

/-! # The actual occurrence-algebra isomorphism and free-variable folds -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) (V : D) (σ π : ℕ → D) (d : ℕ)
variable (S₀ : CategoricalSyntax (E.inverse.obj V)
  (fun n => E.inverse.obj (σ n)) (fun n => E.inverse.obj (π n)) d)
variable (S₁ : CategoricalSyntax V σ π d)
variable (ℓ : E.functor.obj S₀.lists.algebra.carrier ≅ S₁.lists.algebra.carrier)
variable (hnil : E.functor.map S₀.lists.algebra.nil ≫ ℓ.hom =
  terminalComparison E.functor ≫ S₁.lists.algebra.nil)
variable (hsingleton : E.functor.map S₀.lists.singleton ≫ ℓ.hom =
  (E.counitIso.app V).hom ≫ S₁.lists.singleton)
variable (happend : E.functor.map S₀.lists.append ≫ ℓ.hom =
  (SyntaxOptionTransport.productIso E ℓ ℓ).hom ≫ S₁.lists.append)
variable (hdeletion : E.functor.map (S₀.lists.deletion S₀.decidableVariables) ≫ ℓ.hom =
  (SyntaxOptionTransport.productIso E (E.counitIso.app V) ℓ).hom ≫
    S₁.lists.deletion S₁.decidableVariables)

include hnil hsingleton happend in
theorem termOccurrence_structure :
    E.functor.map S₀.occurrenceAlgebra.str.1 ≫ ℓ.hom =
      (termInputIso E ℓ V σ d).hom ≫ S₁.occurrenceAlgebra.str.1 := by
  rw [termInputIso_sum]
  change E.functor.map (coprod.desc S₀.lists.singleton
    (S₀.lists.constructorOccurrences (fun n => E.inverse.obj (σ n)) d)) ≫ ℓ.hom =
      (sumInputIso E (E.counitIso.app V) (constructorInputIso E ℓ σ d)).hom ≫
        coprod.desc S₁.lists.singleton (S₁.lists.constructorOccurrences σ d)
  apply copair_comparison E
  · exact hsingleton
  · exact constructorOccurrences_comparison E S₀.lists S₁.lists ℓ hnil happend σ d

include hnil happend hdeletion in
theorem formulaOccurrence_structure :
    E.functor.map S₀.occurrenceAlgebra.str.2 ≫ ℓ.hom =
      (formulaInputIso E ℓ V π d).hom ≫ S₁.occurrenceAlgebra.str.2 := by
  rw [formulaInputIso_sum]
  change E.functor.map
    (coprod.desc
      (coprod.desc
        (coprod.desc (coprod.desc S₀.lists.append
          (S₀.lists.constructorOccurrences (fun n => E.inverse.obj (π n)) d)) (𝟙 _))
        S₀.lists.append)
      (S₀.lists.deletion S₀.decidableVariables)) ≫ ℓ.hom =
    (sumInputIso E
      (sumInputIso E
        (sumInputIso E
          (sumInputIso E (SyntaxOptionTransport.productIso E ℓ ℓ) (constructorInputIso E ℓ π d)) ℓ)
        (SyntaxOptionTransport.productIso E ℓ ℓ))
      (SyntaxOptionTransport.productIso E (E.counitIso.app V) ℓ)).hom ≫
      coprod.desc
        (coprod.desc
          (coprod.desc (coprod.desc S₁.lists.append (S₁.lists.constructorOccurrences π d)) (𝟙 _))
          S₁.lists.append)
        (S₁.lists.deletion S₁.decidableVariables)
  apply copair_comparison E
  · apply copair_comparison E
    · apply copair_comparison E
      · apply copair_comparison E
        · exact happend
        · exact constructorOccurrences_comparison E S₀.lists S₁.lists ℓ hnil happend π d
      · simp
    · exact happend
  · exact hdeletion

include hnil hsingleton happend hdeletion in
/-- This is an isomorphism of the actual occurrence algebras. Its
constructor proof is derived from the list operations, before any
appeal to the uniqueness of the syntax fold. -/
def occurrenceAlgebraIso :
    AlgebraTransport.mappedAlgebra (E.prod E) (languageJointIso E V σ π d) S₀.occurrenceAlgebra ≅
      S₁.occurrenceAlgebra := by
  refine Endofunctor.Algebra.isoMk (listPairIso E ℓ) ?_
  apply (cancel_epi ((languageJointIso E V σ π d).app S₀.occurrenceAlgebra.a).hom).mp
  change ((languageJointIso E V σ π d).app S₀.occurrenceAlgebra.a).hom ≫
    ((SyntaxPolynomial.jointFunctor (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d)).map (listPairIso E ℓ).hom ≫ S₁.occurrenceAlgebra.str) =
      ((languageJointIso E V σ π d).app S₀.occurrenceAlgebra.a).hom ≫
        ((((languageJointIso E V σ π d).app S₀.occurrenceAlgebra.a).inv ≫
          (E.prod E).functor.map S₀.occurrenceAlgebra.str) ≫ (listPairIso E ℓ).hom)
  simp only [Category.assoc,Iso.hom_inv_id_assoc]
  apply Prod.ext
  · change ((languageJointIso E V σ π d).hom.app
      (S₀.lists.algebra.carrier,S₀.lists.algebra.carrier)).1 ≫
      (SyntaxPolynomial.termExpression V σ d).eval.map (listPairIso E ℓ).hom ≫ S₁.occurrenceAlgebra.str.1 =
        E.functor.map S₀.occurrenceAlgebra.str.1 ≫ ℓ.hom
    rw [language_term_input_assoc]
    exact (termOccurrence_structure E V σ π d S₀ S₁ ℓ hnil hsingleton happend).symm
  · change ((languageJointIso E V σ π d).hom.app
      (S₀.lists.algebra.carrier,S₀.lists.algebra.carrier)).2 ≫
      (SyntaxPolynomial.formulaExpression V π d).eval.map (listPairIso E ℓ).hom ≫ S₁.occurrenceAlgebra.str.2 =
        E.functor.map S₀.occurrenceAlgebra.str.2 ≫ ℓ.hom
    rw [language_formula_input_assoc]
    exact (formulaOccurrence_structure E V σ π d S₀ S₁ ℓ hnil happend hdeletion).symm

variable (c : mappedSyntaxAlgebra E V σ π d S₀ ≅ S₁.algebra)

include hnil hsingleton happend hdeletion in
/-- The two actual algebra morphisms are equal by the proved mapped
initiality. A fold equation is not supplied as a premise. -/
theorem occurrence_fold_comparison :
    (E.prod E).functor.map (S₀.fold S₀.occurrenceAlgebra) ≫ (listPairIso E ℓ).hom =
      c.hom.f ≫ S₁.fold S₁.occurrenceAlgebra := by
  let b := occurrenceAlgebraIso E V σ π d S₀ S₁ ℓ hnil hsingleton happend hdeletion
  have h := (mappedSyntaxInitial E V σ π d S₀).hom_ext
    ((AlgebraTransport.functor (E.prod E) (languageJointIso E V σ π d)).map
      (S₀.initial.to S₀.occurrenceAlgebra) ≫ b.hom)
    (c.hom ≫ S₁.initial.to S₁.occurrenceAlgebra)
  exact congrArg Endofunctor.Algebra.Hom.f h

include hnil hsingleton happend hdeletion in
theorem map_termOccurrences :
    E.functor.map S₀.termOccurrences ≫ ℓ.hom =
      (syntaxTermIso E V σ π d S₀ c).hom ≫ S₁.termOccurrences :=
  congrArg Prod.fst (occurrence_fold_comparison E V σ π d S₀ S₁ ℓ hnil hsingleton happend hdeletion c)

include hnil hsingleton happend hdeletion in
theorem map_formulaOccurrences :
    E.functor.map S₀.formulaOccurrences ≫ ℓ.hom =
      (syntaxFormulaIso E V σ π d S₀ c).hom ≫ S₁.formulaOccurrences :=
  congrArg Prod.snd (occurrence_fold_comparison E V σ π d S₀ S₁ ℓ hnil hsingleton happend hdeletion c)

end CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
