/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxPolynomialNormalization

/-! Actual constructor squares for distinct term/formula carriers.
Coefficient-template equalities are retained as explicit comparison legs. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D)

theorem substitutionNormalizedPolynomial_natural {A A' : C × C} {B B' : D × D}
    (i : (E.prod E).functor.obj A ≅ B) (i' : (E.prod E).functor.obj A' ≅ B')
    (f : A ⟶ A') (g : B ⟶ B')
    (h : (E.prod E).functor.map f ≫ i'.hom = i.hom ≫ g)
    (p : SyntaxPolynomial D) (p₀ : SyntaxPolynomial C) (p₁ : SyntaxPolynomial D)
    (h₀ : p₀ = p.mapCoefficients E.inverse.obj) (h₁ : p.mapCoefficients id = p₁) :
    E.functor.map (p₀.eval.map f) ≫ (normalizedPolynomialIso E A' B' i' p p₀ p₁ h₀ h₁).hom =
      (normalizedPolynomialIso E A B i p p₀ p₁ h₀ h₁).hom ≫ p₁.eval.map g := by
  cases h₀
  cases h₁
  simpa only [normalizedPolynomialIso,eqToIso_refl,Iso.refl_trans,Iso.trans_refl] using
    substitutionPolynomialIso_natural E i i' f g h p

theorem normalizedConstructorSummand_inl (A : C × C) (B : D × D)
    (i : (E.prod E).functor.obj A ≅ B)
    (p q : SyntaxPolynomial D) (p₀ q₀ : SyntaxPolynomial C) (p₁ q₁ : SyntaxPolynomial D)
    (hp₀ : p₀ = p.mapCoefficients E.inverse.obj) (hq₀ : q₀ = q.mapCoefficients E.inverse.obj)
    (hp₁ : p.mapCoefficients id = p₁) (hq₁ : q.mapCoefficients id = q₁)
    {Y : C} {Y' : D} (j : E.functor.obj Y ≅ Y')
    (s : (SyntaxPolynomial.sum p₀ q₀).eval.obj A ⟶ Y)
    (s' : (SyntaxPolynomial.sum p₁ q₁).eval.obj B ⟶ Y')
    (hs : E.functor.map s ≫ j.hom =
      (normalizedPolynomialIso E A B i (.sum p q) (.sum p₀ q₀) (.sum p₁ q₁)
        (congrArg₂ SyntaxPolynomial.sum hp₀ hq₀) (congrArg₂ SyntaxPolynomial.sum hp₁ hq₁)).hom ≫ s') :
    E.functor.map (coprod.inl ≫ s) ≫ j.hom =
      (normalizedPolynomialIso E A B i p p₀ p₁ hp₀ hp₁).hom ≫ coprod.inl ≫ s' := by
  rw [Functor.map_comp,Category.assoc,hs,
    normalizedPolynomialIso_sum E A B i p q p₀ q₀ p₁ q₁ hp₀ hq₀ hp₁ hq₁]
  simp only [Category.assoc,map_inl_inv_coprodComparison_assoc,coprod.inl_map_assoc]

theorem normalizedConstructorSummand_inr (A : C × C) (B : D × D)
    (i : (E.prod E).functor.obj A ≅ B)
    (p q : SyntaxPolynomial D) (p₀ q₀ : SyntaxPolynomial C) (p₁ q₁ : SyntaxPolynomial D)
    (hp₀ : p₀ = p.mapCoefficients E.inverse.obj) (hq₀ : q₀ = q.mapCoefficients E.inverse.obj)
    (hp₁ : p.mapCoefficients id = p₁) (hq₁ : q.mapCoefficients id = q₁)
    {Y : C} {Y' : D} (j : E.functor.obj Y ≅ Y')
    (s : (SyntaxPolynomial.sum p₀ q₀).eval.obj A ⟶ Y)
    (s' : (SyntaxPolynomial.sum p₁ q₁).eval.obj B ⟶ Y')
    (hs : E.functor.map s ≫ j.hom =
      (normalizedPolynomialIso E A B i (.sum p q) (.sum p₀ q₀) (.sum p₁ q₁)
        (congrArg₂ SyntaxPolynomial.sum hp₀ hq₀) (congrArg₂ SyntaxPolynomial.sum hp₁ hq₁)).hom ≫ s') :
    E.functor.map (coprod.inr ≫ s) ≫ j.hom =
      (normalizedPolynomialIso E A B i q q₀ q₁ hq₀ hq₁).hom ≫ coprod.inr ≫ s' := by
  rw [Functor.map_comp,Category.assoc,hs,
    normalizedPolynomialIso_sum E A B i p q p₀ q₀ p₁ q₁ hp₀ hq₀ hp₁ hq₁]
  simp only [Category.assoc,map_inr_inv_coprodComparison_assoc,coprod.inr_map_assoc]

variable (V : D) (σ π : ℕ → D) (d : ℕ)
variable (S₀ : CategoricalSyntax (E.inverse.obj V)
  (fun n => E.inverse.obj (σ n)) (fun n => E.inverse.obj (π n)) d)
variable (S₁ : CategoricalSyntax V σ π d)
variable (c : mappedSyntaxAlgebra E V σ π d S₀ ≅ S₁.algebra)

def syntaxTermConstructorInputIso :
    E.functor.obj ((SyntaxPolynomial.termExpression (E.inverse.obj V)
      (fun n => E.inverse.obj (σ n)) d).eval.obj S₀.algebra.a) ≅
      (SyntaxPolynomial.termExpression V σ d).eval.obj S₁.algebra.a :=
  normalizedPolynomialIso E S₀.algebra.a S₁.algebra.a (syntaxCarrierIso E V σ π d S₀ c)
    (SyntaxPolynomial.termExpression V σ d)
    (SyntaxPolynomial.termExpression (E.inverse.obj V) (fun n => E.inverse.obj (σ n)) d)
    (SyntaxPolynomial.termExpression V σ d)
    (mapCoefficients_termExpression E.inverse.obj V σ d).symm (termTargetExpressionEquality V σ d)

def syntaxFormulaConstructorInputIso :
    E.functor.obj ((SyntaxPolynomial.formulaExpression (E.inverse.obj V)
      (fun n => E.inverse.obj (π n)) d).eval.obj S₀.algebra.a) ≅
      (SyntaxPolynomial.formulaExpression V π d).eval.obj S₁.algebra.a :=
  normalizedPolynomialIso E S₀.algebra.a S₁.algebra.a (syntaxCarrierIso E V σ π d S₀ c)
    (SyntaxPolynomial.formulaExpression V π d)
    (SyntaxPolynomial.formulaExpression (E.inverse.obj V) (fun n => E.inverse.obj (π n)) d)
    (SyntaxPolynomial.formulaExpression V π d)
    (mapCoefficients_formulaExpression E.inverse.obj V π d).symm (formulaTargetExpressionEquality V π d)

def syntaxConstructorsInputIso (α : ℕ → D) (n : ℕ) :
    E.functor.obj ((SyntaxPolynomial.constructors (fun k => E.inverse.obj (α k)) n).eval.obj S₀.algebra.a) ≅
      (SyntaxPolynomial.constructors α n).eval.obj S₁.algebra.a :=
  normalizedPolynomialIso E S₀.algebra.a S₁.algebra.a (syntaxCarrierIso E V σ π d S₀ c)
    (SyntaxPolynomial.constructors α n) (SyntaxPolynomial.constructors (fun k => E.inverse.obj (α k)) n)
    (SyntaxPolynomial.constructors α n)
    (mapCoefficients_constructors E.inverse.obj α n).symm
    (by simpa only [id_eq] using mapCoefficients_constructors (id : D → D) α n)

theorem syntax_term_structure :
    E.functor.map S₀.algebra.str.1 ≫ (syntaxTermIso E V σ π d S₀ c).hom =
      (syntaxTermConstructorInputIso E V σ π d S₀ S₁ c).hom ≫ S₁.algebra.str.1 := by
  have h := congrArg Prod.fst (language_structure_comparison E V σ π d S₀ c)
  change E.functor.map S₀.algebra.str.1 ≫ (syntaxTermIso E V σ π d S₀ c).hom =
    ((languageJointIso E V σ π d).hom.app S₀.algebra.a).1 ≫
      (SyntaxPolynomial.termExpression V σ d).eval.map (syntaxCarrierIso E V σ π d S₀ c).hom ≫
        S₁.algebra.str.1 at h
  rw [← Category.assoc,language_term_map] at h
  simpa only [syntaxTermConstructorInputIso,normalizedPolynomialIso,substitutionPolynomialIso,
    termInputMap,Iso.trans_hom,eqToIso.hom,Functor.mapIso_hom,Category.assoc] using h

theorem syntax_formula_structure :
    E.functor.map S₀.algebra.str.2 ≫ (syntaxFormulaIso E V σ π d S₀ c).hom =
      (syntaxFormulaConstructorInputIso E V σ π d S₀ S₁ c).hom ≫ S₁.algebra.str.2 := by
  have h := congrArg Prod.snd (language_structure_comparison E V σ π d S₀ c)
  change E.functor.map S₀.algebra.str.2 ≫ (syntaxFormulaIso E V σ π d S₀ c).hom =
    ((languageJointIso E V σ π d).hom.app S₀.algebra.a).2 ≫
      (SyntaxPolynomial.formulaExpression V π d).eval.map (syntaxCarrierIso E V σ π d S₀ c).hom ≫
        S₁.algebra.str.2 at h
  rw [← Category.assoc,language_formula_map] at h
  simpa only [syntaxFormulaConstructorInputIso,normalizedPolynomialIso,substitutionPolynomialIso,
    formulaInputMap,Iso.trans_hom,eqToIso.hom,Functor.mapIso_hom,Category.assoc] using h

theorem syntax_variable_constructor :
    E.functor.map S₀.variableConstructor ≫ (syntaxTermIso E V σ π d S₀ c).hom =
      (E.counitIso.app V).hom ≫ S₁.variableConstructor := by
  have h := normalizedConstructorSummand_inl E S₀.algebra.a S₁.algebra.a
    (syntaxCarrierIso E V σ π d S₀ c) (.coefficient V) (SyntaxPolynomial.constructors σ d)
    (.coefficient (E.inverse.obj V)) (SyntaxPolynomial.constructors (fun n => E.inverse.obj (σ n)) d)
    (.coefficient V) (SyntaxPolynomial.constructors σ d) rfl
    (mapCoefficients_constructors E.inverse.obj σ d).symm rfl
    (by simpa only [id_eq] using mapCoefficients_constructors (id : D → D) σ d)
    (syntaxTermIso E V σ π d S₀ c) S₀.algebra.str.1 S₁.algebra.str.1
    (syntax_term_structure E V σ π d S₀ S₁ c)
  simpa only [CategoricalSyntax.variableConstructor,normalizedPolynomialIso_coefficient,
    SyntaxPolynomial.eval,Functor.const_obj_obj] using h

theorem syntax_function_constructors :
    E.functor.map S₀.functionConstructors ≫ (syntaxTermIso E V σ π d S₀ c).hom =
      (syntaxConstructorsInputIso E V σ π d S₀ S₁ c σ d).hom ≫ S₁.functionConstructors := by
  have h := normalizedConstructorSummand_inr E S₀.algebra.a S₁.algebra.a
    (syntaxCarrierIso E V σ π d S₀ c) (.coefficient V) (SyntaxPolynomial.constructors σ d)
    (.coefficient (E.inverse.obj V)) (SyntaxPolynomial.constructors (fun n => E.inverse.obj (σ n)) d)
    (.coefficient V) (SyntaxPolynomial.constructors σ d) rfl
    (mapCoefficients_constructors E.inverse.obj σ d).symm rfl
    (by simpa only [id_eq] using mapCoefficients_constructors (id : D → D) σ d)
    (syntaxTermIso E V σ π d S₀ c) S₀.algebra.str.1 S₁.algebra.str.1
    (syntax_term_structure E V σ π d S₀ S₁ c)
  simpa only [CategoricalSyntax.functionConstructors,syntaxConstructorsInputIso] using h

end CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
