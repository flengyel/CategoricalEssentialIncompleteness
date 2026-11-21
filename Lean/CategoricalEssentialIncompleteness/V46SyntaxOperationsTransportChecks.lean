/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntaxOperationsTransport


/-! # Fold equations under the polynomial and algebra comparisons -/

@[expose] public section
noncomputable section
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransportChecks
open SyntaxOperationsTransport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable (E : C ≌ D) {F₀ : C ⥤ C} {G₀ : D ⥤ D}
variable (α : F₀ ⋙ E.functor ≅ E.functor ⋙ G₀)
example (A B : Endofunctor.Algebra F₀) (hA : IsInitial A) :
    E.functor.map (hA.to B).f =
      ((AlgebraTransport.initial E α A hA).to (AlgebraTransport.mappedAlgebra E α B)).f :=
  mapped_fold_underlying E α A hA B
example (A B : Endofunctor.Algebra F₀) (hA : IsInitial A)
    {A' B' : Endofunctor.Algebra G₀}
    (a : AlgebraTransport.mappedAlgebra E α A ≅ A')
    (b : AlgebraTransport.mappedAlgebra E α B ≅ B') :
    a.inv ≫ (AlgebraTransport.functor E α).map (hA.to B) ≫ b.hom =
      ((AlgebraTransport.initial E α A hA).ofIso a).to B' :=
  mapped_fold_comparison E α A hA B a b

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open SyntacticPredicates SyntacticSyntax
variable [Regular D] [FinitaryExtensive D]
example (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (E' : PredicateCategory T ≌ D)
    (p q : SyntaxPolynomial D)
    (B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
      (p.mapCoefficients E'.inverse.obj) (q.mapCoefficients E'.inverse.obj))) :
    (E'.prod E').functor.map
        ((plainPostfixInitial T (p.mapCoefficients E'.inverse.obj)
          (q.mapCoefficients E'.inverse.obj)).to B).f =
      ((SyntaxPolynomialTransport.initial E' E'.inverse.obj id
        (fun X => E'.counitIso.app X) p q
        (plainPostfixAlgebra T (p.mapCoefficients E'.inverse.obj) (q.mapCoefficients E'.inverse.obj))
        (plainPostfixInitial T (p.mapCoefficients E'.inverse.obj) (q.mapCoefficients E'.inverse.obj))).to
        (SyntacticSyntax.Transport.mappedAlgebra E' E'.inverse.obj id
          (fun X => E'.counitIso.app X) p q B)).f :=
  plain_mapped_fold T E' p q B
end CategoricalEssentialIncompleteness.V46.SyntaxOperationsTransportChecks
