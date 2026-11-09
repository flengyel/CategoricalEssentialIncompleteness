import CategoricalEssentialIncompleteness.V46MillerCanonicalSyntaxComparisonCore

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation
universe v₁ v₂ u₁ u₂

section Generic
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) (V : C) (σ π : ℕ → C) (d : ℕ)
local notation "K₀" => SyntaxPolynomial.jointFunctor (SyntaxPolynomial.termExpression V σ d)
  (SyntaxPolynomial.formulaExpression V π d)
local notation "K₁" => SyntaxPolynomial.jointFunctor
  (SyntaxPolynomial.termExpression (E.functor.obj V) (fun n => E.functor.obj (σ n)) d)
  (SyntaxPolynomial.formulaExpression (E.functor.obj V) (fun n => E.functor.obj (π n)) d)

example (S₀ : CategoricalSyntax V σ π d) :
    (forwardAlgebra E V σ π d S₀).a=(E.prod E).functor.obj S₀.algebra.a :=
  forwardAlgebra_carrier E V σ π d S₀

example (S₀ : CategoricalSyntax V σ π d)
    (S₁ : CategoricalSyntax (E.functor.obj V) (fun n => E.functor.obj (σ n))
      (fun n => E.functor.obj (π n)) d) :
    (K₁).map (forwardAlgebraIso E V σ π d S₀ S₁).hom.f≫S₁.algebra.str=
      (forwardAlgebra E V σ π d S₀).str≫(forwardAlgebraIso E V σ π d S₀ S₁).hom.f :=
  (forwardAlgebraIso E V σ π d S₀ S₁).hom.h

example (S₀ : CategoricalSyntax V σ π d)
    (S₁ : CategoricalSyntax (E.functor.obj V) (fun n => E.functor.obj (σ n))
      (fun n => E.functor.obj (π n)) d) :
    (K₁).map (forwardAlgebraIso E V σ π d S₀ S₁).inv.f≫(forwardAlgebra E V σ π d S₀).str=
      S₁.algebra.str≫(forwardAlgebraIso E V σ π d S₀ S₁).inv.f :=
  (forwardAlgebraIso E V σ π d S₀ S₁).inv.h

example (S₀ : CategoricalSyntax V σ π d) (B : Endofunctor.Algebra (K₀)) :
    (AlgebraTransport.functor (E.prod E) (forwardJointIso E V σ π d)).map (S₀.initial.to B)=
      (forwardInitial E V σ π d S₀).to
        (AlgebraTransport.mappedAlgebra (E.prod E) (forwardJointIso E V σ π d) B) :=
  forward_fold E V σ π d S₀ B

example (S₀ : CategoricalSyntax V σ π d) (B : Endofunctor.Algebra (K₁))
    (f : forwardAlgebra E V σ π d S₀ ⟶ B) :
    f=(forwardInitial E V σ π d S₀).to B := (forwardInitial E V σ π d S₀).hom_ext _ _
end Generic

variable (a : Point) (V : PredicateCategory 𝗣𝗔) (σ π : ℕ → PredicateCategory 𝗣𝗔) (d : ℕ)
local notation "P" => Uniform.Family.ofPoint a
local notation "E" => Total.pointPresentation a
local notation "F" => Syntax.predicateFunctor (P)
local notation "S₁" => NamedSyntaxComparison.presentedSyntax (P) V σ π d
local notation "S₂" => NamedSyntaxComparison.canonicalPresentedSyntax a V σ π d

example : (E).functor.obj (S₁).algebra.a.1 ≅ (S₂).algebra.a.1 :=
  constructorTermIso a V σ π d
example : (E).functor.obj (S₁).algebra.a.2 ≅ (S₂).algebra.a.2 :=
  constructorFormulaIso a V σ π d
example : ((E).prod (E)).functor.map (S₁).algebra.str ≫
      (forwardConstructorAlgebraIso a V σ π d).hom.f =
    (forwardJointIso (E) ((F).obj V) (fun n => (F).obj (σ n))
      (fun n => (F).obj (π n)) d).hom.app (S₁).algebra.a ≫
      (SyntaxPolynomial.jointFunctor
        (SyntaxPolynomial.termExpression ((E).functor.obj ((F).obj V))
          (fun n => (E).functor.obj ((F).obj (σ n))) d)
        (SyntaxPolynomial.formulaExpression ((E).functor.obj ((F).obj V))
          (fun n => (E).functor.obj ((F).obj (π n))) d)).map
        (forwardConstructorAlgebraIso a V σ π d).hom.f ≫ (S₂).algebra.str :=
  constructor_comparison a V σ π d
end CategoricalEssentialIncompleteness.V46.Miller.CanonicalPresentation
