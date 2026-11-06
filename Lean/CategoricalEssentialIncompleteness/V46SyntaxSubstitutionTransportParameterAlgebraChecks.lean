import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportParameterAlgebra

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
    (V : D) (σ π : ℕ → D) (d : ℕ)
    (S₀ : CategoricalSyntax (E.inverse.obj V)
      (fun n => E.inverse.obj (σ n)) (fun n => E.inverse.obj (π n)) d)
    (S₁ : CategoricalSyntax V σ π d)
    (c : mappedSyntaxAlgebra E V σ π d S₀ ≅ S₁.algebra) :
    AlgebraTransport.mappedAlgebra ((sliceEquivalence E b).prod (sliceEquivalence E b))
        (syntaxParameterLanguageIso E b V σ π d)
        (SyntaxPolynomial.algebraWithParameters
          (SyntaxPolynomial.termExpression (E.inverse.obj V) (fun n => E.inverse.obj (σ n)) d)
          (SyntaxPolynomial.formulaExpression (E.inverse.obj V) (fun n => E.inverse.obj (π n)) d)
          S₀.algebra P) ≅
      SyntaxPolynomial.algebraWithParameters (SyntaxPolynomial.termExpression V σ d)
        (SyntaxPolynomial.formulaExpression V π d) S₁.algebra Q :=
  syntaxParameterAlgebraIso E b V σ π d S₀ S₁ c
