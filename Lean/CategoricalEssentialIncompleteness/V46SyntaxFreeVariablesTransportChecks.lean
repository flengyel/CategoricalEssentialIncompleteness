import CategoricalEssentialIncompleteness.V46SyntaxFreeVariablesTransport

noncomputable section
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SyntaxFreeVariablesTransportChecks
open SyntaxOperationsTransport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) (V : D) (σ π : ℕ → D) (d : ℕ)
variable (S₀ : CategoricalSyntax (E.inverse.obj V)
  (fun n => E.inverse.obj (σ n)) (fun n => E.inverse.obj (π n)) d)
variable (S₁ : CategoricalSyntax V σ π d)
variable (ℓ : E.functor.obj S₀.lists.algebra.carrier ≅ S₁.lists.algebra.carrier)
variable (hnil : E.functor.map S₀.lists.algebra.nil ≫ ℓ.hom =
  terminalComparison E.functor ≫ S₁.lists.algebra.nil)
variable (hsingleton : E.functor.map S₀.lists.singleton ≫ ℓ.hom =
  (E.counitIso.app V).hom ≫ S₁.lists.singleton)
variable (happend : E.functor.map S₀.lists.append ≫ ℓ.hom =
  (SyntaxOptionTransport.productIso E ℓ ℓ).hom ≫ S₁.lists.append)
variable (hdeletion : E.functor.map (S₀.lists.deletion S₀.decidableVariables) ≫ ℓ.hom =
  (SyntaxOptionTransport.productIso E (E.counitIso.app V) ℓ).hom ≫
    S₁.lists.deletion S₁.decidableVariables)

example (c : mappedSyntaxAlgebra E V σ π d S₀ ≅ S₁.algebra) :
    E.functor.map S₀.formulaOccurrences ≫ ℓ.hom =
      (syntaxFormulaIso E V σ π d S₀ c).hom ≫ S₁.formulaOccurrences :=
  map_formulaOccurrences E V σ π d S₀ S₁ ℓ hnil hsingleton happend hdeletion c
example (c : mappedSyntaxAlgebra E V σ π d S₀ ≅ S₁.algebra) :
    E.functor.map S₀.termOccurrences ≫ ℓ.hom =
      (syntaxTermIso E V σ π d S₀ c).hom ≫ S₁.termOccurrences :=
  map_termOccurrences E V σ π d S₀ S₁ ℓ hnil hsingleton happend hdeletion c
end CategoricalEssentialIncompleteness.V46.SyntaxFreeVariablesTransportChecks
