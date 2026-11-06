import CategoricalEssentialIncompleteness.V46SyntaxLanguageTransportComponents

noncomputable section
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SyntaxLanguageTransportComponentsChecks
open SyntaxOperationsTransport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) (V : D) (σ π : ℕ → D) (d : ℕ)
example (A : C × C) (B : D × D) (k : (E.prod E).functor.obj A ⟶ B) :
    ((languageJointIso E V σ π d).hom.app A).1 ≫ (SyntaxPolynomial.termExpression V σ d).eval.map k =
      termInputMap E V σ d A B k := language_term_map E V σ π d A B k
example (A : C × C) (B : D × D) (k : (E.prod E).functor.obj A ⟶ B) :
    ((languageJointIso E V σ π d).hom.app A).2 ≫ (SyntaxPolynomial.formulaExpression V π d).eval.map k =
      formulaInputMap E V π d A B k := language_formula_map E V σ π d A B k
end CategoricalEssentialIncompleteness.V46.SyntaxLanguageTransportComponentsChecks
