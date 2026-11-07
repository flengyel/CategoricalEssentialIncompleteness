import CategoricalEssentialIncompleteness.V46ArithmeticIndexedFibersTransport
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u₁ u₂ v₁ v₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers.InferenceTransport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [Regular D] [HasFiniteCoproducts C] [HasFiniteCoproducts D]
variable (E : C ≌ D) {F : C} {N : ℕ} (R : RulePresentation F N)
variable (R' : RulePresentation (E.functor.obj F) N) (h : Data E R R')
example : R.inference ⋙ (Over.postEquiv F E).functor ≅
    (Over.postEquiv F E).functor ⋙ R'.inference := comparison E R R' h
example : Endofunctor.Algebra R.inference ≌ Endofunctor.Algebra R'.inference := algebraEquivalence E R R' h
end CategoricalEssentialIncompleteness.V46.ArithmeticIndexedFibers.InferenceTransport
