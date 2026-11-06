/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportInputs

/-! # Explicit normalization of polynomial comparison isomorphisms -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) (A : C × C) (B : D × D) (i : (E.prod E).functor.obj A ≅ B)

/-- These are explicit object-equality legs, around the existing
constructor-preserving comparison at arbitrary, distinct sort pairs. -/
def normalizedPolynomialIso (p : SyntaxPolynomial D) (p₀ : SyntaxPolynomial C) (p₁ : SyntaxPolynomial D)
    (h₀ : p₀ = p.mapCoefficients E.inverse.obj) (h₁ : p.mapCoefficients id = p₁) :
    E.functor.obj (p₀.eval.obj A) ≅ p₁.eval.obj B :=
  eqToIso (congrArg (fun r => E.functor.obj (r.eval.obj A)) h₀) ≪≫
    substitutionPolynomialIso E A B i p ≪≫ eqToIso (congrArg (fun r => r.eval.obj B) h₁)

theorem normalizedPolynomialIso_cast (p : SyntaxPolynomial D) (p₀ : SyntaxPolynomial C) (p₁ : SyntaxPolynomial D)
    (h₀ : p₀ = p.mapCoefficients E.inverse.obj) (h₁ : p.mapCoefficients id = p₁)
    {ht : (E.functor.obj ((p.mapCoefficients E.inverse.obj).eval.obj A) ≅
      (p.mapCoefficients id).eval.obj B) = (E.functor.obj (p₀.eval.obj A) ≅ p₁.eval.obj B)} :
    (cast ht (substitutionPolynomialIso E A B i p)).hom =
      (normalizedPolynomialIso E A B i p p₀ p₁ h₀ h₁).hom := by
  rw [iso_cast_hom (congrArg (fun r => E.functor.obj (r.eval.obj A)) h₀.symm)
    (congrArg (fun r => r.eval.obj B) h₁)]
  rfl

theorem substitutionPolynomialIso_sum (p q : SyntaxPolynomial D) :
    (substitutionPolynomialIso E A B i (.sum p q)).hom =
      (inv (coprodComparison E.functor
        ((p.mapCoefficients E.inverse.obj).eval.obj A) ((q.mapCoefficients E.inverse.obj).eval.obj A))) ≫
        coprod.map (substitutionPolynomialIso E A B i p).hom (substitutionPolynomialIso E A B i q).hom := by
  apply (cancel_epi (coprodComparison E.functor
    ((p.mapCoefficients E.inverse.obj).eval.obj A) ((q.mapCoefficients E.inverse.obj).eval.obj A))).mp
  apply coprod.hom_ext
  · rw [← Category.assoc,coprodComparison_inl,substitutionPolynomialIso_inl]
    simp only [← Category.assoc,coprodComparison_inl,map_inl_inv_coprodComparison,coprod.inl_map]
  · rw [← Category.assoc,coprodComparison_inr,substitutionPolynomialIso_inr]
    simp only [← Category.assoc,coprodComparison_inr,map_inr_inv_coprodComparison,coprod.inr_map]

theorem normalizedPolynomialIso_product
    (p q : SyntaxPolynomial D) (p₀ q₀ : SyntaxPolynomial C) (p₁ q₁ : SyntaxPolynomial D)
    (hp₀ : p₀ = p.mapCoefficients E.inverse.obj) (hq₀ : q₀ = q.mapCoefficients E.inverse.obj)
    (hp₁ : p.mapCoefficients id = p₁) (hq₁ : q.mapCoefficients id = q₁) :
    (normalizedPolynomialIso E A B i (.product p q) (.product p₀ q₀) (.product p₁ q₁)
      (congrArg₂ SyntaxPolynomial.product hp₀ hq₀) (congrArg₂ SyntaxPolynomial.product hp₁ hq₁)).hom =
      (SyntaxOptionTransport.productIso E
        (normalizedPolynomialIso E A B i p p₀ p₁ hp₀ hp₁)
        (normalizedPolynomialIso E A B i q q₀ q₁ hq₀ hq₁)).hom := by
  cases hp₀
  cases hq₀
  cases hp₁
  cases hq₁
  simpa only [normalizedPolynomialIso,eqToIso_refl,Iso.refl_trans,Iso.trans_refl] using
    substitutionPolynomialIso_product E A B i p q

theorem normalizedPolynomialIso_sum
    (p q : SyntaxPolynomial D) (p₀ q₀ : SyntaxPolynomial C) (p₁ q₁ : SyntaxPolynomial D)
    (hp₀ : p₀ = p.mapCoefficients E.inverse.obj) (hq₀ : q₀ = q.mapCoefficients E.inverse.obj)
    (hp₁ : p.mapCoefficients id = p₁) (hq₁ : q.mapCoefficients id = q₁) :
    (normalizedPolynomialIso E A B i (.sum p q) (.sum p₀ q₀) (.sum p₁ q₁)
      (congrArg₂ SyntaxPolynomial.sum hp₀ hq₀) (congrArg₂ SyntaxPolynomial.sum hp₁ hq₁)).hom =
      inv (coprodComparison E.functor (p₀.eval.obj A) (q₀.eval.obj A)) ≫
        coprod.map (normalizedPolynomialIso E A B i p p₀ p₁ hp₀ hp₁).hom
          (normalizedPolynomialIso E A B i q q₀ q₁ hq₀ hq₁).hom := by
  cases hp₀
  cases hq₀
  cases hp₁
  cases hq₁
  simpa only [normalizedPolynomialIso,Iso.trans_hom,eqToIso.hom,eqToHom_refl,
    Category.id_comp,Category.comp_id] using substitutionPolynomialIso_sum E A B i p q

@[simp] theorem normalizedPolynomialIso_term :
    (normalizedPolynomialIso E A B i .term .term .term rfl rfl).hom = i.hom.1 := by
  simp only [normalizedPolynomialIso,Iso.trans_hom,eqToIso.hom,eqToHom_refl,
    Category.id_comp,Category.comp_id,substitutionPolynomialIso_term]

@[simp] theorem normalizedPolynomialIso_formula :
    (normalizedPolynomialIso E A B i .formula .formula .formula rfl rfl).hom = i.hom.2 := by
  simp only [normalizedPolynomialIso,Iso.trans_hom,eqToIso.hom,eqToHom_refl,
    Category.id_comp,Category.comp_id,substitutionPolynomialIso_formula]

@[simp] theorem normalizedPolynomialIso_coefficient (X : D) :
    (normalizedPolynomialIso E A B i (.coefficient X) (.coefficient (E.inverse.obj X)) (.coefficient X)
      rfl rfl).hom = (E.counitIso.app X).hom := by
  simp only [normalizedPolynomialIso,Iso.trans_hom,eqToIso.hom,eqToHom_refl,
    Category.id_comp,Category.comp_id,substitutionPolynomialIso_coefficient]

end CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
