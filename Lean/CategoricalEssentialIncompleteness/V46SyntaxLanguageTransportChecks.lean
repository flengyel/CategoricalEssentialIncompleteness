import CategoricalEssentialIncompleteness.V46SyntaxLanguageTransport

noncomputable section
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SyntaxLanguageTransportChecks
open SyntaxOperationsTransport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) (V : D) (σ π : ℕ → D) (d : ℕ)
variable (S₀ : CategoricalSyntax (E.inverse.obj V)
  (fun n => E.inverse.obj (σ n)) (fun n => E.inverse.obj (π n)) d)
variable (S₁ : CategoricalSyntax V σ π d)
variable (c : mappedSyntaxAlgebra E V σ π d S₀ ≅ S₁.algebra)
example : IsInitial (mappedSyntaxAlgebra E V σ π d S₀) := mappedSyntaxInitial E V σ π d S₀
example : (E.prod E).functor.map S₀.algebra.str ≫ c.hom.f =
    (languageJointIso E V σ π d).hom.app S₀.algebra.a ≫
      (SyntaxPolynomial.jointFunctor (SyntaxPolynomial.termExpression V σ d)
        (SyntaxPolynomial.formulaExpression V π d)).map c.hom.f ≫ S₁.algebra.str :=
  language_structure_comparison E V σ π d S₀ c
end CategoricalEssentialIncompleteness.V46.SyntaxLanguageTransportChecks
