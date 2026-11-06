import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportNormalizedFamilies

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
    (A : C × C) (B : D × D) (i : (E.prod E).functor.obj A ≅ B)
    (p : SyntaxPolynomial D) (p₀ : SyntaxPolynomial C) (p₁ : SyntaxPolynomial D)
    (h₀ : p.mapCoefficients E.inverse.obj = p₀) (h₁ : p.mapCoefficients id = p₁)
    {Z : C} {Z' : D} (j : E.functor.obj Z ≅ Z')
    (h : P ⨯ p₀.eval.obj A ⟶ Z) (h' : Q ⨯ p₁.eval.obj B ⟶ Z')
    (hh : E.functor.map h ≫ j.hom =
      (SyntaxOptionTransport.productIso E b (substitutionNormalizedInputIso E A B i p p₀ p₁ h₀ h₁)).hom ≫ h') :
    (sliceEquivalence E b).functor.map
        (SyntaxPolynomial.parameterComparison P A p₀ ≫ parameterHom h) ≫
          (coefficientComparison E b Z Z' j).hom =
      (substitutionNormalizedParameterInputIso E b A B i p p₀ p₁ h₀ h₁).hom ≫
        SyntaxPolynomial.parameterComparison Q B p₁ ≫ parameterHom h' :=
  map_substitution_normalizedParameterOperation E b A B i p p₀ p₁ h₀ h₁ j h h' hh
