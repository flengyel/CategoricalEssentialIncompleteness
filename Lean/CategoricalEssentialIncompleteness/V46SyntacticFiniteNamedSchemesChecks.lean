import CategoricalEssentialIncompleteness.V46SyntacticFiniteNamedSchemes

noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SyntacticFiniteNamedSchemes.Checks
variable {C : Type u} [Category.{v} C] [Regular C] [FinitaryExtensive C]
variable {V : C} {σ π : ℕ → C} {d : ℕ} (S : CategoricalSyntax V σ π d)

example (i : Fin 7) : schemeInjection S i ≫ S.logicalAxioms = schemeMorphism S i :=
  schemeInjection_formula S i

example : schemeParameters S 3 = S.instantiationParameters := rfl
example : schemeParameters S 6 = S.equalitySchemeParameters := rfl
end CategoricalEssentialIncompleteness.V46.SyntacticFiniteNamedSchemes.Checks
