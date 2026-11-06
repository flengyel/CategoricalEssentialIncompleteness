import CategoricalEssentialIncompleteness.V46SyntaxSubstitutionTransportConstructorsCore

/-! Function substitution transports by the actual two projection
squares and the ordinary constructor square. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) (V : D) (σ π : ℕ → D) (d : ℕ)
variable (S₀ : CategoricalSyntax (E.inverse.obj V)
  (fun n => E.inverse.obj (σ n)) (fun n => E.inverse.obj (π n)) d)
variable (S₁ : CategoricalSyntax V σ π d)
variable (c : mappedSyntaxAlgebra E V σ π d S₀ ≅ S₁.algebra)

def substitutionStateInputIso (p : SyntaxPolynomial D) :=
  substitutionPolynomialIso E S₀.substitutionCarriers S₁.substitutionCarriers
    (substitutionStateIso E V σ π d S₀ S₁ c) p

def substitutionStateConstructorsInputIso (α : ℕ → D) (n : ℕ) :
    E.functor.obj ((SyntaxPolynomial.constructors (fun k => E.inverse.obj (α k)) n).eval.obj
      S₀.substitutionCarriers) ≅ (SyntaxPolynomial.constructors α n).eval.obj S₁.substitutionCarriers :=
  normalizedPolynomialIso E S₀.substitutionCarriers S₁.substitutionCarriers
    (substitutionStateIso E V σ π d S₀ S₁ c) (SyntaxPolynomial.constructors α n)
    (SyntaxPolynomial.constructors (fun k => E.inverse.obj (α k)) n) (SyntaxPolynomial.constructors α n)
    (mapCoefficients_constructors E.inverse.obj α n).symm
    (by simpa only [id_eq] using mapCoefficients_constructors (id : D → D) α n)

theorem map_functionSubstitutionPair :
    E.functor.map S₀.functionSubstitutionPair ≫
        (substitutionTermStateIso E V σ π d S₀ S₁ c).hom =
      (substitutionStateConstructorsInputIso E V σ π d S₀ S₁ c σ d).hom ≫
        S₁.functionSubstitutionPair := by
  have ho := substitutionNormalizedPolynomial_natural E
    (substitutionStateIso E V σ π d S₀ S₁ c) (syntaxCarrierIso E V σ π d S₀ c)
    S₀.originalProjection S₁.originalProjection
    (substitutionOriginal_comparison E V σ π d S₀ S₁ c) (SyntaxPolynomial.constructors σ d)
    (SyntaxPolynomial.constructors (fun n => E.inverse.obj (σ n)) d) (SyntaxPolynomial.constructors σ d)
    (mapCoefficients_constructors E.inverse.obj σ d).symm
    (by simpa only [id_eq] using mapCoefficients_constructors (id : D → D) σ d)
  have hr := substitutionNormalizedPolynomial_natural E
    (substitutionStateIso E V σ π d S₀ S₁ c) (syntaxCarrierIso E V σ π d S₀ c)
    S₀.termResultProjection S₁.termResultProjection
    (substitutionTermResult_comparison E V σ π d S₀ S₁ c) (SyntaxPolynomial.constructors σ d)
    (SyntaxPolynomial.constructors (fun n => E.inverse.obj (σ n)) d) (SyntaxPolynomial.constructors σ d)
    (mapCoefficients_constructors E.inverse.obj σ d).symm
    (by simpa only [id_eq] using mapCoefficients_constructors (id : D → D) σ d)
  change E.functor.map ((SyntaxPolynomial.constructors (fun n => E.inverse.obj (σ n)) d).eval.map
      S₀.originalProjection) ≫ (syntaxConstructorsInputIso E V σ π d S₀ S₁ c σ d).hom =
    (substitutionStateConstructorsInputIso E V σ π d S₀ S₁ c σ d).hom ≫
      (SyntaxPolynomial.constructors σ d).eval.map S₁.originalProjection at ho
  change E.functor.map ((SyntaxPolynomial.constructors (fun n => E.inverse.obj (σ n)) d).eval.map
      S₀.termResultProjection) ≫ (syntaxConstructorsInputIso E V σ π d S₀ S₁ c σ d).hom =
    (substitutionStateConstructorsInputIso E V σ π d S₀ S₁ c σ d).hom ≫
      (SyntaxPolynomial.constructors σ d).eval.map S₁.termResultProjection at hr
  change E.functor.map (prod.lift _ _) ≫
    (SyntaxOptionTransport.productIso E (syntaxTermIso E V σ π d S₀ c)
      (syntaxTermIso E V σ π d S₀ c)).hom = _ ≫ prod.lift _ _
  rw [SyntaxOptionTransport.map_lift,prod.comp_lift]
  apply congrArg₂ (fun f g => prod.lift f g)
  · change E.functor.map
      ((SyntaxPolynomial.constructors (fun n => E.inverse.obj (σ n)) d).eval.map
        S₀.originalProjection ≫ S₀.functionConstructors) ≫
        (syntaxTermIso E V σ π d S₀ c).hom =
      (substitutionStateConstructorsInputIso E V σ π d S₀ S₁ c σ d).hom ≫
        ((SyntaxPolynomial.constructors σ d).eval.map S₁.originalProjection ≫ S₁.functionConstructors)
    rw [E.functor.map_comp,Category.assoc,syntax_function_constructors,
      ← Category.assoc,ho,Category.assoc]
  · change E.functor.map
      ((SyntaxPolynomial.constructors (fun n => E.inverse.obj (σ n)) d).eval.map
        S₀.termResultProjection ≫ S₀.functionConstructors) ≫
        (syntaxTermIso E V σ π d S₀ c).hom =
      (substitutionStateConstructorsInputIso E V σ π d S₀ S₁ c σ d).hom ≫
        ((SyntaxPolynomial.constructors σ d).eval.map S₁.termResultProjection ≫ S₁.functionConstructors)
    rw [E.functor.map_comp,Category.assoc,syntax_function_constructors,
      ← Category.assoc,hr,Category.assoc]

end CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
