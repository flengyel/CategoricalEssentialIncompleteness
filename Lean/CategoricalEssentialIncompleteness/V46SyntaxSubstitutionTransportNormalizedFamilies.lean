/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportFamilies
public import CategoricalEssentialIncompleteness.V46SyntaxPolynomialNormalization

/-! Explicit polynomial equalities normalize base and parameter-slice
inputs together. The transport proof reduces to the actual raw square;
no cast of an entire initial algebra is required. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
open SyntacticLists.Transport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) {P : C} {Q : D} (b : E.functor.obj P ≅ Q)
variable (A : C × C) (B : D × D) (i : (E.prod E).functor.obj A ≅ B)
variable (p : SyntaxPolynomial D) (p₀ : SyntaxPolynomial C) (p₁ : SyntaxPolynomial D)
variable (h₀ : p.mapCoefficients E.inverse.obj = p₀) (h₁ : p.mapCoefficients id = p₁)

def substitutionNormalizedInputIso : E.functor.obj (p₀.eval.obj A) ≅ p₁.eval.obj B :=
  normalizedPolynomialIso E A B i p p₀ p₁ h₀.symm h₁

def substitutionNormalizedParameterInputIso :
    (sliceEquivalence E b).functor.obj ((p₀.withParameters P).eval.obj
      (constantFamily P A.1,constantFamily P A.2)) ≅
      (p₁.withParameters Q).eval.obj (constantFamily Q B.1,constantFamily Q B.2) :=
  (eqToIso (congrArg (fun q => (sliceEquivalence E b).functor.obj
    ((q.withParameters P).eval.obj (constantFamily P A.1,constantFamily P A.2))) h₀)).symm ≪≫
    substitutionParameterInputIso E b A B i p ≪≫
      eqToIso (congrArg (fun q => (q.withParameters Q).eval.obj
        (constantFamily Q B.1,constantFamily Q B.2)) h₁)

/-- Equalities supplied here concern only the coefficient templates.
The operation square is ordinary constructor coherence; the resulting
parameter-slice square is proved, not supplied. -/
theorem map_substitution_normalizedParameterOperation {Z : C} {Z' : D}
    (j : E.functor.obj Z ≅ Z') (h : P ⨯ p₀.eval.obj A ⟶ Z)
    (h' : Q ⨯ p₁.eval.obj B ⟶ Z')
    (hh : E.functor.map h ≫ j.hom =
      (SyntaxOptionTransport.productIso E b (substitutionNormalizedInputIso E A B i p p₀ p₁ h₀ h₁)).hom ≫ h') :
    (sliceEquivalence E b).functor.map
        (SyntaxPolynomial.parameterComparison P A p₀ ≫ parameterHom h) ≫
          (coefficientComparison E b Z Z' j).hom =
      (substitutionNormalizedParameterInputIso E b A B i p p₀ p₁ h₀ h₁).hom ≫
        SyntaxPolynomial.parameterComparison Q B p₁ ≫ parameterHom h' := by
  subst p₀
  subst p₁
  have hh' : E.functor.map h ≫ j.hom =
      (SyntaxOptionTransport.productIso E b (substitutionPolynomialIso E A B i p)).hom ≫ h' := by
    simpa only [substitutionNormalizedInputIso,normalizedPolynomialIso,eqToIso_refl,
      Iso.refl_trans,Iso.trans_refl] using hh
  simpa only [substitutionNormalizedParameterInputIso,eqToIso_refl,Iso.refl_symm,
    Iso.refl_trans,Iso.trans_refl] using map_substitution_parameterOperation E b A B i p j h h' hh'

theorem substitutionNormalizedParameterCopair_square
    (q : SyntaxPolynomial D) (q₀ : SyntaxPolynomial C) (q₁ : SyntaxPolynomial D)
    (hq₀ : q.mapCoefficients E.inverse.obj = q₀) (hq₁ : q.mapCoefficients id = q₁)
    {Z : C} {Z' : D} (j : E.functor.obj Z ≅ Z')
    (f : (p₀.withParameters P).eval.obj (constantFamily P A.1,constantFamily P A.2) ⟶ constantFamily P Z)
    (g : (q₀.withParameters P).eval.obj (constantFamily P A.1,constantFamily P A.2) ⟶ constantFamily P Z)
    (f' : (p₁.withParameters Q).eval.obj (constantFamily Q B.1,constantFamily Q B.2) ⟶ constantFamily Q Z')
    (g' : (q₁.withParameters Q).eval.obj (constantFamily Q B.1,constantFamily Q B.2) ⟶ constantFamily Q Z')
    (hf : (sliceEquivalence E b).functor.map f ≫ (coefficientComparison E b Z Z' j).hom =
      (substitutionNormalizedParameterInputIso E b A B i p p₀ p₁ h₀ h₁).hom ≫ f')
    (hg : (sliceEquivalence E b).functor.map g ≫ (coefficientComparison E b Z Z' j).hom =
      (substitutionNormalizedParameterInputIso E b A B i q q₀ q₁ hq₀ hq₁).hom ≫ g') :
    (sliceEquivalence E b).functor.map (coprod.desc f g) ≫ (coefficientComparison E b Z Z' j).hom =
      (substitutionNormalizedParameterInputIso E b A B i (.sum p q) (.sum p₀ q₀) (.sum p₁ q₁)
        (congrArg₂ SyntaxPolynomial.sum h₀ hq₀) (congrArg₂ SyntaxPolynomial.sum h₁ hq₁)).hom ≫
          coprod.desc f' g' := by
  subst p₀
  subst q₀
  subst p₁
  subst q₁
  have hf' : (sliceEquivalence E b).functor.map f ≫ (coefficientComparison E b Z Z' j).hom =
      (substitutionParameterInputIso E b A B i p).hom ≫ f' := by
    simpa only [substitutionNormalizedParameterInputIso,eqToIso_refl,Iso.refl_symm,
      Iso.refl_trans,Iso.trans_refl] using hf
  have hg' : (sliceEquivalence E b).functor.map g ≫ (coefficientComparison E b Z Z' j).hom =
      (substitutionParameterInputIso E b A B i q).hom ≫ g' := by
    simpa only [substitutionNormalizedParameterInputIso,eqToIso_refl,Iso.refl_symm,
      Iso.refl_trans,Iso.trans_refl] using hg
  simp only [substitutionNormalizedParameterInputIso,eqToIso_refl,Iso.refl_symm,
    Iso.trans_hom,Iso.refl_hom,Category.comp_id]
  erw [Category.id_comp]
  exact substitutionParameterCopair_square E b A B i p q j f g f' g' hf' hg'

end CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
