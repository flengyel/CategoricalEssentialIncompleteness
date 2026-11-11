/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalSyntax
public import CategoricalEssentialIncompleteness.V46AlgebraTransport
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-! # Two-sorted polynomial comparison with arbitrary coefficient labels -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂ w
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46
namespace SyntaxPolynomial
variable {I : Type w} {C : Type u₁}

/-- Relabel the coefficient positions, retaining both recursive sorts
and the exact terminal, product and coproduct expression. -/
def mapCoefficients (f : I → C) : SyntaxPolynomial I → SyntaxPolynomial C
  | .term => .term
  | .formula => .formula
  | .coefficient i => .coefficient (f i)
  | .unit => .unit
  | .product a b => .product (mapCoefficients f a) (mapCoefficients f b)
  | .sum a b => .sum (mapCoefficients f a) (mapCoefficients f b)

end SyntaxPolynomial

namespace SyntaxPolynomialTransport
variable {I : Type w} {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₂} D]
variable [HasFiniteProducts C] [HasFiniteCoproducts C]
variable [HasFiniteProducts D] [HasFiniteCoproducts D]
variable (E : C ≌ D) (f : I → C) (g : I → D)
variable (χ : ∀ i, E.functor.obj (f i) ≅ g i)

/-- Coefficient isomorphisms are indexed by template labels, so distinct
positions may have the same source object and different target objects. -/
def component : (p : SyntaxPolynomial I) → (X : C × C) →
    E.functor.obj ((p.mapCoefficients f).eval.obj X) ≅
      (p.mapCoefficients g).eval.obj ((E.prod E).functor.obj X)
  | .term, _ => Iso.refl _
  | .formula, _ => Iso.refl _
  | .coefficient i, _ => χ i
  | .unit, _ => asIso (terminalComparison E.functor)
  | .product a b, X =>
      asIso (prodComparison E.functor ((a.mapCoefficients f).eval.obj X)
        ((b.mapCoefficients f).eval.obj X)) ≪≫
          prod.mapIso (component a X) (component b X)
  | .sum a b, X =>
      (asIso (coprodComparison E.functor ((a.mapCoefficients f).eval.obj X)
        ((b.mapCoefficients f).eval.obj X))).symm ≪≫
          coprod.mapIso (component a X) (component b X)

theorem component_natural (p : SyntaxPolynomial I) {X Y : C × C} (k : X ⟶ Y) :
    E.functor.map ((p.mapCoefficients f).eval.map k) ≫ (component E f g χ p Y).hom =
      (component E f g χ p X).hom ≫
        (p.mapCoefficients g).eval.map ((E.prod E).functor.map k) := by
  induction p generalizing X Y with
  | term => simp [component, SyntaxPolynomial.mapCoefficients, SyntaxPolynomial.eval]
  | formula => simp [component, SyntaxPolynomial.mapCoefficients, SyntaxPolynomial.eval]
  | coefficient i => simp [component, SyntaxPolynomial.mapCoefficients, SyntaxPolynomial.eval]
  | unit => simp [component, SyntaxPolynomial.mapCoefficients, SyntaxPolynomial.eval]
  | product a b ia ib =>
      change E.functor.map (prod.map _ _) ≫
        (prodComparison E.functor _ _ ≫ prod.map _ _) =
          (prodComparison E.functor _ _ ≫ prod.map _ _) ≫ prod.map _ _
      rw [← Category.assoc, prodComparison_natural, Category.assoc, prod.map_map,
        ia k, ib k]
      simp only [Category.assoc, prod.map_map]
  | sum a b ia ib =>
      change E.functor.map (coprod.map _ _) ≫
        (inv (coprodComparison E.functor _ _) ≫ coprod.map _ _) =
          (inv (coprodComparison E.functor _ _) ≫ coprod.map _ _) ≫ coprod.map _ _
      apply (cancel_epi (coprodComparison E.functor
        ((a.mapCoefficients f).eval.obj X) ((b.mapCoefficients f).eval.obj X))).mp
      rw [← Category.assoc, coprodComparison_natural]
      simp only [Category.assoc, IsIso.hom_inv_id_assoc, coprod.map_map]
      rw [ia k, ib k]

/-- The entire endofunctor comparison is natural in both recursive sorts. -/
def naturalIso (p : SyntaxPolynomial I) :
    (p.mapCoefficients f).eval ⋙ E.functor ≅
      (E.prod E).functor ⋙ (p.mapCoefficients g).eval :=
  NatIso.ofComponents (component E f g χ p) (fun k => component_natural E f g χ p k)

/-- The paired comparison uses the product equivalence on the actual
term/formula algebra categories. -/
def jointIso (p q : SyntaxPolynomial I) :
    SyntaxPolynomial.jointFunctor (p.mapCoefficients f) (q.mapCoefficients f) ⋙
        (E.prod E).functor ≅
      (E.prod E).functor ⋙
        SyntaxPolynomial.jointFunctor (p.mapCoefficients g) (q.mapCoefficients g) := by
  refine NatIso.ofComponents (fun X => ?_) ?_
  · exact { hom := ((component E f g χ p X).hom, (component E f g χ q X).hom)
            inv := ((component E f g χ p X).inv, (component E f g χ q X).inv)
            hom_inv_id := by ext <;> simp [SyntaxPolynomial.jointFunctor]
            inv_hom_id := by ext <;> simp [SyntaxPolynomial.jointFunctor] }
  · intro X Y k
    exact Prod.ext (component_natural E f g χ p k) (component_natural E f g χ q k)

/-- Initiality is transported only after constructing the complete
two-sorted polynomial and algebra-category comparisons. -/
def algebraEquivalence (p q : SyntaxPolynomial I) :
    Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
        (p.mapCoefficients f) (q.mapCoefficients f)) ≌
      Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
        (p.mapCoefficients g) (q.mapCoefficients g)) :=
  AlgebraTransport.equivalence (E.prod E) (jointIso E f g χ p q)

def initial (p q : SyntaxPolynomial I)
    (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
      (p.mapCoefficients f) (q.mapCoefficients f))) (h : IsInitial A) :
    IsInitial (AlgebraTransport.mappedAlgebra (E.prod E) (jointIso E f g χ p q) A) :=
  AlgebraTransport.initial (E.prod E) (jointIso E f g χ p q) A h

end SyntaxPolynomialTransport
end CategoricalEssentialIncompleteness.V46
