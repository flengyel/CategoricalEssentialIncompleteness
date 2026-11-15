/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46ArithmeticSignedTotal
public import CategoricalEssentialIncompleteness.V46SyntaxOperationsTransport

/-! # Free syntax underlying the transported arithmetic signed calculus

The equivalence transports the two recursive sorts and every coefficient.
Initiality in every parameter slice is constructed for this algebra.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.ForwardSyntaxTransport
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [Regular D] [FinitaryExtensive C] [FinitaryExtensive D]

def castAlgebra {p q r s : SyntaxPolynomial C} (hp : p = r) (hq : q = s)
    (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p q)) :
    Endofunctor.Algebra (SyntaxPolynomial.jointFunctor r s) :=
  Eq.mp (congrArg (fun K => Endofunctor.Algebra K)
    (congrArg₂ SyntaxPolynomial.jointFunctor hp hq)) A

def castInitial {p q r s : SyntaxPolynomial C} (hp : p = r) (hq : q = s)
    (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p q)) (hA : IsInitial A) :
    IsInitial (castAlgebra hp hq A) := by
  cases hp
  cases hq
  exact hA

def castStable {p q r s : SyntaxPolynomial C} (hp : p = r) (hq : q = s)
    (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p q))
    (hA : ∀ R, IsInitial (SyntaxPolynomial.algebraWithParameters p q A R)) :
    ∀ R, IsInitial (SyntaxPolynomial.algebraWithParameters r s (castAlgebra hp hq A) R) := by
  cases hp
  cases hq
  exact hA

variable (E : C ≌ D) (p q : SyntaxPolynomial C)
variable (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p q))

def sourceAlgebra : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
    (p.mapCoefficients id) (q.mapCoefficients id)) :=
  castAlgebra (SyntacticSyntax.mapCoefficients_id p).symm
    (SyntacticSyntax.mapCoefficients_id q).symm A

def algebra : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
    (p.mapCoefficients E.functor.obj) (q.mapCoefficients E.functor.obj)) :=
  SyntacticSyntax.Transport.mappedAlgebra E id E.functor.obj (fun _ => Iso.refl _)
    p q (sourceAlgebra p q A)

def initial (hA : IsInitial A) : IsInitial (algebra E p q A) :=
  SyntaxPolynomialTransport.initial E id E.functor.obj (fun _ => Iso.refl _) p q
    (sourceAlgebra p q A)
    (castInitial (SyntacticSyntax.mapCoefficients_id p).symm
      (SyntacticSyntax.mapCoefficients_id q).symm A hA)

def stable (hA : ∀ R, IsInitial (SyntaxPolynomial.algebraWithParameters p q A R)) (R : D) :
    IsInitial (SyntaxPolynomial.algebraWithParameters (p.mapCoefficients E.functor.obj)
      (q.mapCoefficients E.functor.obj) (algebra E p q A) R) :=
  SyntacticSyntax.Transport.mappedStable E id E.functor.obj (fun _ => Iso.refl _) p q
    (sourceAlgebra p q A)
    (castStable (SyntacticSyntax.mapCoefficients_id p).symm
      (SyntacticSyntax.mapCoefficients_id q).symm A hA) R

/-- Every fold, including the parameterized syntax folds, is transported
by the constructed algebra comparison. -/
theorem mapped_fold (hA : IsInitial A)
    (B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
      (p.mapCoefficients id) (q.mapCoefficients id))) :
    (E.prod E).functor.map
      ((castInitial (SyntacticSyntax.mapCoefficients_id p).symm
        (SyntacticSyntax.mapCoefficients_id q).symm A hA).to B).f =
    ((initial E p q A hA).to
      (SyntacticSyntax.Transport.mappedAlgebra E id E.functor.obj
        (fun _ => Iso.refl _) p q B)).f :=
  SyntaxOperationsTransport.mapped_fold_underlying (E.prod E)
    (SyntaxPolynomialTransport.jointIso E id E.functor.obj (fun _ => Iso.refl _) p q)
    (sourceAlgebra p q A)
    (castInitial (SyntacticSyntax.mapCoefficients_id p).symm
      (SyntacticSyntax.mapCoefficients_id q).symm A hA) B

theorem cast_carrier {p q r s : SyntaxPolynomial C} (hp : p = r) (hq : q = s)
    (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p q)) :
    (castAlgebra hp hq A).a = A.a := by
  cases hp
  cases hq
  rfl

theorem source_carrier : (sourceAlgebra p q A).a = A.a :=
  cast_carrier _ _ _

theorem carrier : (algebra E p q A).a = (E.prod E).functor.obj A.a := by
  change (E.prod E).functor.obj (sourceAlgebra p q A).a = _
  rw [source_carrier]

end CategoricalEssentialIncompleteness.V46.ForwardSyntaxTransport

namespace CategoricalEssentialIncompleteness.V46.ArithmeticSignedTotal
local notation "G" => SyntacticPredicates.realization 𝗣𝗔
local notation "E" => predicateEquivalence 𝗣𝗔
local notation "N" => (PrintedObjectCoding.Number : PredicateCategory 𝗣𝗔)
variable {V : PredicateCategory 𝗣𝗔} (F : NullaryPresentations V)
local notation "S" => NullaryPresentations.syntaxData F N
local notation "p" => SyntaxPolynomial.termExpression V (fun _ => ⊥_ (PredicateCategory 𝗣𝗔)) 0
local notation "q" => SyntaxPolynomial.formulaExpression V (fun _ => N) 0

/-- The transported term/formula algebra is free on the displayed
coefficient objects. Its no-function coefficient is an initial object. -/
def syntaxAlgebra : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
    (SyntaxPolynomial.termExpression ((G).obj V)
      (fun _ => (G).obj (⊥_ (PredicateCategory 𝗣𝗔))) 0)
    (SyntaxPolynomial.formulaExpression ((G).obj V) (fun _ => (G).obj N) 0)) :=
  ForwardSyntaxTransport.castAlgebra
    (SyntaxOperationsTransport.mapCoefficients_termExpression (G).obj V
      (fun _ => ⊥_ (PredicateCategory 𝗣𝗔)) 0)
    (SyntaxOperationsTransport.mapCoefficients_formulaExpression (G).obj V (fun _ => N) 0)
    (ForwardSyntaxTransport.algebra (E) p q (S).algebra)

def syntaxInitial : IsInitial (syntaxAlgebra F) :=
  ForwardSyntaxTransport.castInitial _ _ _
    (ForwardSyntaxTransport.initial (E) p q (S).algebra (S).initial)

def syntaxStable (P : TotalSplit 𝗣𝗔) : IsInitial
    (SyntaxPolynomial.algebraWithParameters
      (SyntaxPolynomial.termExpression ((G).obj V)
        (fun _ => (G).obj (⊥_ (PredicateCategory 𝗣𝗔))) 0)
      (SyntaxPolynomial.formulaExpression ((G).obj V) (fun _ => (G).obj N) 0)
      (syntaxAlgebra F) P) :=
  ForwardSyntaxTransport.castStable _ _ _
    (ForwardSyntaxTransport.stable (E) p q (S).algebra (S).stable) P

theorem syntax_carrier : (syntaxAlgebra F).a =
    ((G).obj (S).algebra.a.1, (G).obj (S).algebra.a.2) := by
  rw [syntaxAlgebra, ForwardSyntaxTransport.cast_carrier, ForwardSyntaxTransport.carrier]
  rfl

def noFunctions : IsInitial ((G).obj (⊥_ (PredicateCategory 𝗣𝗔))) :=
  IsInitial.isInitialObj (G) _ initialIsInitial

end CategoricalEssentialIncompleteness.V46.ArithmeticSignedTotal
