/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SyntacticSyntaxFamilyTransport
public import CategoricalEssentialIncompleteness.V46SyntaxPolynomialTransport

/-! # Polynomial comparisons in arbitrary parameter slices -/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v₁ v₂ u₁ u₂ w
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Transport
open SyntacticLists.Transport

variable {I : Type w} {C : Type u₁} {D : Type u₂}
variable [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [FinitaryExtensive C] [Regular D] [FinitaryExtensive D]
variable (E : C ≌ D) {P : C} {Q : D} (b : E.functor.obj P ≅ Q)
variable (f : I → C) (g : I → D) (χ : ∀ i, E.functor.obj (f i) ≅ g i)

/-- The canonical slice comparison retains the literal withParameters
polynomials. It therefore requires no casts of an endofunctor algebra. -/
def sliceComponent : (p : SyntaxPolynomial I) → (X : Over P × Over P) →
    (sliceEquivalence E b).functor.obj (((p.mapCoefficients f).withParameters P).eval.obj X) ≅
      ((p.mapCoefficients g).withParameters Q).eval.obj
        (((sliceEquivalence E b).prod (sliceEquivalence E b)).functor.obj X)
  | .term, _ => Iso.refl _
  | .formula, _ => Iso.refl _
  | .coefficient i, _ => coefficientComparison E b (f i) (g i) (χ i)
  | .unit, _ => asIso (terminalComparison (sliceEquivalence E b).functor)
  | .product a c, X =>
      asIso (prodComparison (sliceEquivalence E b).functor
        (((a.mapCoefficients f).withParameters P).eval.obj X)
        (((c.mapCoefficients f).withParameters P).eval.obj X)) ≪≫
          prod.mapIso (sliceComponent a X) (sliceComponent c X)
  | .sum a c, X =>
      (asIso (coprodComparison (sliceEquivalence E b).functor
        (((a.mapCoefficients f).withParameters P).eval.obj X)
        (((c.mapCoefficients f).withParameters P).eval.obj X))).symm ≪≫
          coprod.mapIso (sliceComponent a X) (sliceComponent c X)

theorem sliceComponent_natural (p : SyntaxPolynomial I)
    {X Y : Over P × Over P} (k : X ⟶ Y) :
    (sliceEquivalence E b).functor.map
        (((p.mapCoefficients f).withParameters P).eval.map k) ≫
      (sliceComponent E b f g χ p Y).hom =
        (sliceComponent E b f g χ p X).hom ≫
          ((p.mapCoefficients g).withParameters Q).eval.map
            (((sliceEquivalence E b).prod (sliceEquivalence E b)).functor.map k) := by
  induction p generalizing X Y with
  | term => simp [sliceComponent, SyntaxPolynomial.mapCoefficients,
      SyntaxPolynomial.withParameters, SyntaxPolynomial.eval]
  | formula => simp [sliceComponent, SyntaxPolynomial.mapCoefficients,
      SyntaxPolynomial.withParameters, SyntaxPolynomial.eval]
  | coefficient i => simp [sliceComponent, SyntaxPolynomial.mapCoefficients,
      SyntaxPolynomial.withParameters, SyntaxPolynomial.eval]
  | unit => simp [sliceComponent, SyntaxPolynomial.mapCoefficients,
      SyntaxPolynomial.withParameters, SyntaxPolynomial.eval]
  | product a c ia ic =>
      change (sliceEquivalence E b).functor.map (prod.map _ _) ≫
          (prodComparison (sliceEquivalence E b).functor _ _ ≫ prod.map _ _) =
        (prodComparison (sliceEquivalence E b).functor _ _ ≫ prod.map _ _) ≫ prod.map _ _
      rw [← Category.assoc, prodComparison_natural, Category.assoc,
        prod.map_map, ia k, ic k]
      simp only [Category.assoc, prod.map_map]
  | sum a c ia ic =>
      change (sliceEquivalence E b).functor.map (coprod.map _ _) ≫
          (inv (coprodComparison (sliceEquivalence E b).functor _ _) ≫ coprod.map _ _) =
        (inv (coprodComparison (sliceEquivalence E b).functor _ _) ≫ coprod.map _ _) ≫
          coprod.map _ _
      apply (cancel_epi (coprodComparison (sliceEquivalence E b).functor
        (((a.mapCoefficients f).withParameters P).eval.obj X)
        (((c.mapCoefficients f).withParameters P).eval.obj X))).mp
      rw [← Category.assoc, coprodComparison_natural]
      simp only [Category.assoc, IsIso.hom_inv_id_assoc, coprod.map_map]
      rw [ia k, ic k]

/-- This is a natural isomorphism on all slice families, rather than
only on constant families or on a proposed initial carrier. -/
def sliceNaturalIso (p : SyntaxPolynomial I) :
    ((p.mapCoefficients f).withParameters P).eval ⋙ (sliceEquivalence E b).functor ≅
      ((sliceEquivalence E b).prod (sliceEquivalence E b)).functor ⋙
        ((p.mapCoefficients g).withParameters Q).eval :=
  NatIso.ofComponents (sliceComponent E b f g χ p)
    (fun k => sliceComponent_natural E b f g χ p k)

def sliceJointIso (p q : SyntaxPolynomial I) :
    SyntaxPolynomial.jointFunctor ((p.mapCoefficients f).withParameters P)
        ((q.mapCoefficients f).withParameters P) ⋙
      ((sliceEquivalence E b).prod (sliceEquivalence E b)).functor ≅
        ((sliceEquivalence E b).prod (sliceEquivalence E b)).functor ⋙
          SyntaxPolynomial.jointFunctor ((p.mapCoefficients g).withParameters Q)
            ((q.mapCoefficients g).withParameters Q) := by
  refine NatIso.ofComponents (fun X => ?_) ?_
  · exact
      { hom := ((sliceComponent E b f g χ p X).hom,
          (sliceComponent E b f g χ q X).hom)
        inv := ((sliceComponent E b f g χ p X).inv,
          (sliceComponent E b f g χ q X).inv)
        hom_inv_id := by ext <;> simp [SyntaxPolynomial.jointFunctor]
        inv_hom_id := by ext <;> simp [SyntaxPolynomial.jointFunctor] }
  · intro X Y k
    exact Prod.ext (sliceComponent_natural E b f g χ p k)
      (sliceComponent_natural E b f g χ q k)

/-- The two actual constant-family carrier isomorphisms, paired in the
category on which the two-sorted algebra endofunctor acts. -/
def carrierComparison (X : C × C) :
    (((sliceEquivalence E b).prod (sliceEquivalence E b)).functor.obj
      (constantFamily P X.1, constantFamily P X.2)) ≅
      (constantFamily Q (E.functor.obj X.1), constantFamily Q (E.functor.obj X.2)) where
  hom := ((familyComparison E b X.1).hom, (familyComparison E b X.2).hom)
  inv := ((familyComparison E b X.1).inv, (familyComparison E b X.2).inv)
  hom_inv_id := by ext <;> simp
  inv_hom_id := by ext <;> simp <;> rfl

/-- The slice polynomial comparison followed by the canonical family
comparisons on both recursive sorts. -/
def parameterComponent (p : SyntaxPolynomial I) (X : C × C) :
    (sliceEquivalence E b).functor.obj
        (((p.mapCoefficients f).withParameters P).eval.obj
          (constantFamily P X.1, constantFamily P X.2)) ≅
      ((p.mapCoefficients g).withParameters Q).eval.obj
        (constantFamily Q (E.functor.obj X.1), constantFamily Q (E.functor.obj X.2)) :=
  sliceComponent E b f g χ p (constantFamily P X.1, constantFamily P X.2) ≪≫
    ((p.mapCoefficients g).withParameters Q).eval.mapIso (carrierComparison E b X)

end CategoricalEssentialIncompleteness.V46.SyntacticSyntax.Transport
