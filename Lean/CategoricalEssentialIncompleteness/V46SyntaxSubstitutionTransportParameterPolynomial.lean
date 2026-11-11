/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportNormalizedFamilies

/-! The full two-sorted parameter polynomial is normalized by the same
coefficient equalities as its component operations. This uses finite
products/coproducts in slices, without a RegularOver hypothesis. -/

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
variable (p q : SyntaxPolynomial D) (p₀ q₀ : SyntaxPolynomial C) (p₁ q₁ : SyntaxPolynomial D)
variable (hp₀ : p₀ = p.mapCoefficients E.inverse.obj) (hq₀ : q₀ = q.mapCoefficients E.inverse.obj)
variable (hp₁ : p.mapCoefficients id = p₁) (hq₁ : q.mapCoefficients id = q₁)

include hp₀ hq₀ in
omit [Regular D] [FinitaryExtensive D] in
theorem sourceParameterFunctorEquality :
    SyntaxPolynomial.jointFunctor (p₀.withParameters P) (q₀.withParameters P) =
      SyntaxPolynomial.jointFunctor ((p.mapCoefficients E.inverse.obj).withParameters P)
        ((q.mapCoefficients E.inverse.obj).withParameters P) :=
  congrArg₂ SyntaxPolynomial.jointFunctor
    (congrArg (fun r => r.withParameters P) hp₀) (congrArg (fun r => r.withParameters P) hq₀)

include hp₁ hq₁ in
theorem targetParameterFunctorEquality :
    SyntaxPolynomial.jointFunctor ((p.mapCoefficients id).withParameters Q)
        ((q.mapCoefficients id).withParameters Q) =
      SyntaxPolynomial.jointFunctor (p₁.withParameters Q) (q₁.withParameters Q) :=
  congrArg₂ SyntaxPolynomial.jointFunctor
    (congrArg (fun r => r.withParameters Q) hp₁) (congrArg (fun r => r.withParameters Q) hq₁)

def normalizedParameterJointIso :
    SyntaxPolynomial.jointFunctor (p₀.withParameters P) (q₀.withParameters P) ⋙
        ((sliceEquivalence E b).prod (sliceEquivalence E b)).functor ≅
      ((sliceEquivalence E b).prod (sliceEquivalence E b)).functor ⋙
        SyntaxPolynomial.jointFunctor (p₁.withParameters Q) (q₁.withParameters Q) :=
  eqToIso (congrArg (fun F => F ⋙ ((sliceEquivalence E b).prod (sliceEquivalence E b)).functor)
    (sourceParameterFunctorEquality E p q p₀ q₀ hp₀ hq₀)) ≪≫
    SyntacticSyntax.Transport.sliceJointIso E b E.inverse.obj id (fun X => E.counitIso.app X) p q ≪≫
      eqToIso (congrArg (fun G => ((sliceEquivalence E b).prod (sliceEquivalence E b)).functor ⋙ G)
        (targetParameterFunctorEquality p q p₁ q₁ hp₁ hq₁))

@[reassoc] theorem normalizedParameterJointIso_fst (X : C × C) (Y : D × D)
    (i : (E.prod E).functor.obj X ≅ Y) :
    ((normalizedParameterJointIso E b p q p₀ q₀ p₁ q₁ hp₀ hq₀ hp₁ hq₁).hom.app
      (constantFamily P X.1,constantFamily P X.2)).1 ≫
        (p₁.withParameters Q).eval.map (substitutionFamilyPairIso E b X Y i).hom =
      (substitutionNormalizedParameterInputIso E b X Y i p p₀ p₁ hp₀.symm hp₁).hom := by
  cases hp₀
  cases hq₀
  cases hp₁
  cases hq₁
  simp only [normalizedParameterJointIso,
    substitutionNormalizedParameterInputIso,eqToIso_refl,Iso.refl_symm,Iso.refl_trans,Iso.trans_refl]
  rfl

@[reassoc] theorem normalizedParameterJointIso_snd (X : C × C) (Y : D × D)
    (i : (E.prod E).functor.obj X ≅ Y) :
    ((normalizedParameterJointIso E b p q p₀ q₀ p₁ q₁ hp₀ hq₀ hp₁ hq₁).hom.app
      (constantFamily P X.1,constantFamily P X.2)).2 ≫
        (q₁.withParameters Q).eval.map (substitutionFamilyPairIso E b X Y i).hom =
      (substitutionNormalizedParameterInputIso E b X Y i q q₀ q₁ hq₀.symm hq₁).hom := by
  cases hp₀
  cases hq₀
  cases hp₁
  cases hq₁
  simp only [normalizedParameterJointIso,
    substitutionNormalizedParameterInputIso,eqToIso_refl,Iso.refl_symm,Iso.refl_trans,Iso.trans_refl]
  rfl

end CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
