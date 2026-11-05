/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxStableTransport
import CategoricalEssentialIncompleteness.V46SyntacticSyntaxPlain

/-! # Fold equations under the actual polynomial and algebra comparisons -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂ w
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport

section Algebras
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable (E : C ≌ D) {F₀ : C ⥤ C} {G₀ : D ⥤ D}
variable (α : F₀ ⋙ E.functor ≅ E.functor ⋙ G₀)
variable (A : Endofunctor.Algebra F₀) (hA : IsInitial A)

/-- Mapping the actual initial fold gives the actual target fold. This
is an equality of algebra morphisms, hence includes constructor compatibility. -/
theorem mapped_fold (B : Endofunctor.Algebra F₀) :
    (AlgebraTransport.functor E α).map (hA.to B) =
      (AlgebraTransport.initial E α A hA).to (AlgebraTransport.mappedAlgebra E α B) :=
  (AlgebraTransport.initial E α A hA).hom_ext _ _

theorem mapped_fold_underlying (B : Endofunctor.Algebra F₀) :
    E.functor.map (hA.to B).f =
      ((AlgebraTransport.initial E α A hA).to (AlgebraTransport.mappedAlgebra E α B)).f :=
  congrArg Endofunctor.Algebra.Hom.f (mapped_fold E α A hA B)

/-- Actual constructor-preserving comparison isomorphisms transport the
fold through their hom and inverse, without any numerical identity premise. -/
theorem mapped_fold_comparison (B : Endofunctor.Algebra F₀)
    {A' B' : Endofunctor.Algebra G₀}
    (a : AlgebraTransport.mappedAlgebra E α A ≅ A')
    (b : AlgebraTransport.mappedAlgebra E α B ≅ B') :
    a.inv ≫ (AlgebraTransport.functor E α).map (hA.to B) ≫ b.hom =
      ((AlgebraTransport.initial E α A hA).ofIso a).to B' :=
  ((AlgebraTransport.initial E α A hA).ofIso a).hom_ext _ _

end Algebras

section Concrete
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open SyntacticPredicates SyntacticSyntax
variable {D : Type u₂} [Category.{v₂} D] [Regular D] [FinitaryExtensive D]
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (E : PredicateCategory T ≌ D)
variable (p q : SyntaxPolynomial D)
local notation "a" => SyntaxPolynomial.mapCoefficients E.inverse.obj p
local notation "b" => SyntaxPolynomial.mapCoefficients E.inverse.obj q

/-- The concrete source fold is the proved plain postfix fold. The
target comparison uses the actual counit at each coefficient object. -/
theorem plain_mapped_fold
    (B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor a b)) :
    (E.prod E).functor.map ((plainPostfixInitial T a b).to B).f =
      ((SyntaxPolynomialTransport.initial E E.inverse.obj id
        (fun X => E.counitIso.app X) p q (plainPostfixAlgebra T a b)
          (plainPostfixInitial T a b)).to
        (SyntacticSyntax.Transport.mappedAlgebra E E.inverse.obj id
          (fun X => E.counitIso.app X) p q B)).f :=
  mapped_fold_underlying (E.prod E)
    (SyntaxPolynomialTransport.jointIso E E.inverse.obj id
      (fun X => E.counitIso.app X) p q)
    (plainPostfixAlgebra T a b) (plainPostfixInitial T a b) B

end Concrete

section Coefficients
variable {I : Type w} {C : Type u₁} (f : I → C)

@[simp] theorem mapCoefficients_power (p : SyntaxPolynomial I) (n : ℕ) :
    (SyntaxPolynomial.power p n).mapCoefficients f =
      SyntaxPolynomial.power (p.mapCoefficients f) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      cases n with
      | zero => rfl
      | succ n => simp only [SyntaxPolynomial.power,SyntaxPolynomial.mapCoefficients,ih]

@[simp] theorem mapCoefficients_constructors (σ : ℕ → I) (d : ℕ) :
    (SyntaxPolynomial.constructors σ d).mapCoefficients f =
      SyntaxPolynomial.constructors (fun n => f (σ n)) d := by
  induction d with
  | zero => rfl
  | succ d ih =>
      simp only [SyntaxPolynomial.constructors,SyntaxPolynomial.mapCoefficients,
        mapCoefficients_power,ih]

@[simp] theorem mapCoefficients_termExpression (V : I) (σ : ℕ → I) (d : ℕ) :
    (SyntaxPolynomial.termExpression V σ d).mapCoefficients f =
      SyntaxPolynomial.termExpression (f V) (fun n => f (σ n)) d := by
  simp only [SyntaxPolynomial.termExpression,SyntaxPolynomial.mapCoefficients,
    mapCoefficients_constructors]

@[simp] theorem mapCoefficients_formulaExpression (V : I) (π : ℕ → I) (d : ℕ) :
    (SyntaxPolynomial.formulaExpression V π d).mapCoefficients f =
      SyntaxPolynomial.formulaExpression (f V) (fun n => f (π n)) d := by
  simp only [SyntaxPolynomial.formulaExpression,SyntaxPolynomial.mapCoefficients,
    mapCoefficients_power,mapCoefficients_constructors]

end Coefficients
end CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransport
