import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportConstructorsCore

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
open CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) (V : D) (σ π : ℕ → D) (d : ℕ)
variable (S₀ : CategoricalSyntax (E.inverse.obj V)
  (fun n => E.inverse.obj (σ n)) (fun n => E.inverse.obj (π n)) d)
variable (S₁ : CategoricalSyntax V σ π d)
variable (c : mappedSyntaxAlgebra E V σ π d S₀ ≅ S₁.algebra)

example : E.functor.map S₀.variableConstructor ≫ (syntaxTermIso E V σ π d S₀ c).hom =
    (E.counitIso.app V).hom ≫ S₁.variableConstructor :=
  syntax_variable_constructor E V σ π d S₀ S₁ c

example : E.functor.map S₀.functionConstructors ≫ (syntaxTermIso E V σ π d S₀ c).hom =
    (syntaxConstructorsInputIso E V σ π d S₀ S₁ c σ d).hom ≫ S₁.functionConstructors :=
  syntax_function_constructors E V σ π d S₀ S₁ c
