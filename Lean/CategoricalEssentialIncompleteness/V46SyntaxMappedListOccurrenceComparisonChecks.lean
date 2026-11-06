import CategoricalEssentialIncompleteness.V46SyntaxMappedListOccurrenceComparison

noncomputable section
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SyntaxMappedListOccurrenceComparisonChecks
open SyntaxOperationsTransport SyntacticLists.Transport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) (V : D) (σ π : ℕ → D) (d : ℕ)
variable (S₀ : CategoricalSyntax (E.inverse.obj V)
  (fun n => E.inverse.obj (σ n)) (fun n => E.inverse.obj (π n)) d)
variable (S₁ : CategoricalSyntax V σ π d)
variable (hLists : S₁.lists = mappedStableListAlgebra E (E.inverse.obj V) V
  (E.counitIso.app V) S₀.lists)
variable (c : mappedSyntaxAlgebra E V σ π d S₀ ≅ S₁.algebra)
example : E.functor.map S₀.termOccurrences ≫ (syntaxListIso E V σ π d S₀ S₁ hLists).hom =
    (syntaxTermIso (S₁ := S₁) E V σ π d S₀ c).hom ≫ S₁.termOccurrences :=
  (termOccurrenceComparison_iff E V σ π d S₀ S₁ hLists c).mp
    (mapped_termOccurrence_comparison E V σ π d S₀ S₁ hLists c)
example : E.functor.map S₀.formulaOccurrences ≫ (syntaxListIso E V σ π d S₀ S₁ hLists).hom =
    (syntaxFormulaIso (S₁ := S₁) E V σ π d S₀ c).hom ≫ S₁.formulaOccurrences :=
  (formulaOccurrenceComparison_iff E V σ π d S₀ S₁ hLists c).mp
    (mapped_formulaOccurrence_comparison E V σ π d S₀ S₁ hLists c)
end CategoricalEssentialIncompleteness.V46.SyntaxMappedListOccurrenceComparisonChecks
