import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportInputs

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

example : E.functor.obj S₀.substitutionParameters ≅ S₁.substitutionParameters :=
  substitutionParameterIso E V σ π d S₀ S₁ c

example : E.functor.obj S₀.substitutionCarriers.2 ≅ S₁.substitutionCarriers.2 :=
  substitutionFormulaStateIso E V σ π d S₀ S₁ c

example : E.functor.obj ((SyntaxPolynomial.constructors (fun n => E.inverse.obj (σ n)) d).eval.obj
      S₀.substitutionCarriers) ≅ (SyntaxPolynomial.constructors σ d).eval.obj S₁.substitutionCarriers :=
  substitutionConstructorsInputIso E S₀.substitutionCarriers S₁.substitutionCarriers
    (substitutionStateIso E V σ π d S₀ S₁ c) σ d

example :
    (E.prod E).functor.map S₀.originalProjection ≫ (syntaxCarrierIso E V σ π d S₀ c).hom =
      (substitutionStateIso E V σ π d S₀ S₁ c).hom ≫ S₁.originalProjection :=
  substitutionOriginal_comparison E V σ π d S₀ S₁ c
