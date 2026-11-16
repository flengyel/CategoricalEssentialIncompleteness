/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46DiagramPolynomialComparison

/-! # Initiality for the canonical two-sorted polynomial on numerical diagrams -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.NumericalCanonicalDiagramSyntax
abbrev C := NumericalTuples.Object
variable {J : Type u} [Category.{v} J] {I : Type w}
variable (c : I → J ⥤ C) (p q : SyntaxPolynomial I)

def polynomial : ((J ⥤ C) × (J ⥤ C)) ⥤ ((J ⥤ C) × (J ⥤ C)) :=
  SyntaxPolynomial.jointFunctor (p.mapCoefficients c) (q.mapCoefficients c)

abbrev pairing : ((J ⥤ C) × (J ⥤ C)) ≌ (J ⥤ C × C) := functorProdFunctorEquiv J C C

def comparisonHom (X : (J ⥤ C) × (J ⥤ C)) :
    pairing.functor.obj ((polynomial c p q).obj X) ⟶
      (DiagramInitialAlgebras.diagonal (NumericalDiagramSyntax.polynomials c p q)).obj
        (pairing.functor.obj X) where
  app j := (DiagramPolynomialComparison.component c X p j,
    DiagramPolynomialComparison.component c X q j)
  naturality {j k} f := by
    apply Prod.ext
    · exact (DiagramPolynomialComparison.component_transition c X p f).trans
        (congrArg (fun n => DiagramPolynomialComparison.component c X p j ≫ n)
          (DiagramPolynomialComparison.transition_eq c X p f))
    · exact (DiagramPolynomialComparison.component_transition c X q f).trans
        (congrArg (fun n => DiagramPolynomialComparison.component c X q j ≫ n)
          (DiagramPolynomialComparison.transition_eq c X q f))

instance comparisonHom_isIso (X : (J ⥤ C) × (J ⥤ C)) :
    IsIso (comparisonHom c p q X) := by
  have (j : J) : IsIso ((comparisonHom c p q X).app j) := by
    rw [isIso_prod_iff]
    change IsIso (DiagramPolynomialComparison.component c X p j) ∧
      IsIso (DiagramPolynomialComparison.component c X q j)
    exact ⟨inferInstance, inferInstance⟩
  exact NatIso.isIso_of_isIso_app _

/-- The complete polynomial comparison is natural in both recursive
carriers, not just in the index of the coefficient diagrams. -/
def polynomialIso :
    polynomial c p q ⋙ pairing.functor ≅ pairing.functor ⋙
      DiagramInitialAlgebras.diagonal (NumericalDiagramSyntax.polynomials c p q) :=
  NatIso.ofComponents (fun X => asIso (comparisonHom c p q X)) (by
    intro X Y m
    apply NatTrans.ext
    funext j
    apply Prod.ext
    · exact LaxPolynomialComparison.naturality ((evaluation J C).obj j)
        (fun _ => 𝟙 _) p m
    · exact LaxPolynomialComparison.naturality ((evaluation J C).obj j)
        (fun _ => 𝟙 _) q m)

/-- Every algebra and every algebra morphism is included in the
comparison between the canonical and componentwise polynomial categories. -/
def algebraEquivalence : Endofunctor.Algebra (polynomial c p q) ≌
    Endofunctor.Algebra
      (DiagramInitialAlgebras.diagonal (NumericalDiagramSyntax.polynomials c p q)) :=
  AlgebraTransport.equivalence pairing (polynomialIso c p q)

/-- The carrier is obtained by splitting the term and formula diagrams of
the already constructed numerical initial algebra. -/
def algebra : Endofunctor.Algebra (polynomial c p q) :=
  AlgebraTransport.liftedAlgebra pairing (polynomialIso c p q)
    (NumericalDiagramSyntax.algebra c p q)

def initial : IsInitial (algebra c p q) :=
  (AlgebraTransport.initialIff pairing (polynomialIso c p q) (algebra c p q)).symm
    ((NumericalDiagramSyntax.initial c p q).ofIso
      (AlgebraTransport.mappedLiftIso pairing (polynomialIso c p q)
        (NumericalDiagramSyntax.algebra c p q)).symm)

/-- This identifies the actual lifted algebra, including its constructor,
with the previously proved componentwise numerical algebra. -/
def constructorIso :
    AlgebraTransport.mappedAlgebra pairing (polynomialIso c p q) (algebra c p q) ≅
      NumericalDiagramSyntax.algebra c p q :=
  AlgebraTransport.mappedLiftIso pairing (polynomialIso c p q) _

def fold (B : Endofunctor.Algebra (polynomial c p q)) : algebra c p q ⟶ B :=
  (initial c p q).to B

theorem fold_constructor (B : Endofunctor.Algebra (polynomial c p q)) :
    (polynomial c p q).map (fold c p q B).f ≫ B.str =
      (algebra c p q).str ≫ (fold c p q B).f := (fold c p q B).h

/-- Uniqueness ranges over every underlying pair of natural morphisms. -/
theorem fold_underlying_unique (B : Endofunctor.Algebra (polynomial c p q))
    (m : (algebra c p q).a ⟶ B.a)
    (hm : (polynomial c p q).map m ≫ B.str = (algebra c p q).str ≫ m) :
    m = (fold c p q B).f :=
  congrArg Endofunctor.Algebra.Hom.f ((initial c p q).hom_ext
    (⟨m, hm⟩ : algebra c p q ⟶ B) _)

/-- The actual term/formula expressions of the canonical syntax interface
have a constructed initial algebra, at every finite signature bound. -/
def syntaxData (V : J ⥤ C) (σ π : ℕ → J ⥤ C) (d : ℕ) :
    Σ A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
      (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)),
      IsInitial A := by
  let r := SyntaxPolynomial.termExpression V σ d
  let s := SyntaxPolynomial.formulaExpression V π d
  have h : (Σ A : Endofunctor.Algebra (polynomial id r s), IsInitial A) :=
    ⟨algebra id r s, initial id r s⟩
  have he : polynomial id r s = SyntaxPolynomial.jointFunctor r s := by
    unfold polynomial
    rw [SyntaxPolynomial.mapCoefficients_id r, SyntaxPolynomial.mapCoefficients_id s]
  rw [he] at h
  exact h

end CategoricalEssentialIncompleteness.V46.NumericalCanonicalDiagramSyntax
