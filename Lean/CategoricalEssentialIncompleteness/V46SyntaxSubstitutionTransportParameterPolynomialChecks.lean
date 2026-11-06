import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportParameterPolynomial

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
open CategoricalEssentialIncompleteness.V46.SyntacticLists.Transport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]

example (E : C ≌ D) {P : C} {Q : D} (b : E.functor.obj P ≅ Q)
    (p q : SyntaxPolynomial D) (p₀ q₀ : SyntaxPolynomial C) (p₁ q₁ : SyntaxPolynomial D)
    (hp₀ : p₀ = p.mapCoefficients E.inverse.obj) (hq₀ : q₀ = q.mapCoefficients E.inverse.obj)
    (hp₁ : p.mapCoefficients id = p₁) (hq₁ : q.mapCoefficients id = q₁) :
    SyntaxPolynomial.jointFunctor (p₀.withParameters P) (q₀.withParameters P) ⋙
        ((sliceEquivalence E b).prod (sliceEquivalence E b)).functor ≅
      ((sliceEquivalence E b).prod (sliceEquivalence E b)).functor ⋙
        SyntaxPolynomial.jointFunctor (p₁.withParameters Q) (q₁.withParameters Q) :=
  normalizedParameterJointIso E b p q p₀ q₀ p₁ q₁ hp₀ hq₀ hp₁ hq₁
