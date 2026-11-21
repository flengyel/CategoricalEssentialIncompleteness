/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerSyntaxPresentation
public import CategoricalEssentialIncompleteness.V46MillerTotalExtensive
public import CategoricalEssentialIncompleteness.V46PredicateInterpretationRegular
public import CategoricalEssentialIncompleteness.V46SyntaxPolynomialTransport

/-! # The original syntax polynomial under the ordinary word inclusion

Finite geometry is proved through the standard-model comparison and reflection by the
uniform carrier functor. This inclusion is not assumed faithful or to preserve
initiality. Its algebra only transports the existing word carriers and constructor
operations; the new universal property needs a fold into every uniform target algebra.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.Miller.Syntax
variable (P : Uniform.Family)

instance predicateFunctor_preservesFiniteLimits : PreservesFiniteLimits (predicateFunctor P) := by
  let : PreservesFiniteLimits (predicateFunctor P ⋙ Total.underlying) :=
    preservesFiniteLimits_of_natIso (standardComparison P).symm
  exact preservesFiniteLimits_of_reflects_of_preserves (predicateFunctor P) Total.underlying

instance predicateFunctor_preservesFiniteCoproducts : PreservesFiniteCoproducts (predicateFunctor P) := by
  let : PreservesFiniteCoproducts (Total.underlying (P := P)) := ⟨fun _ => inferInstance⟩
  let : PreservesFiniteCoproducts (predicateFunctor P ⋙ Total.underlying) :=
    ⟨fun _ => preservesColimitsOfShape_of_natIso (standardComparison P).symm⟩
  exact preservesFiniteCoproducts_of_reflects_of_preserves (predicateFunctor P) Total.underlying

namespace Polynomial

abbrev mapped (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) : SyntaxPolynomial (Total.TotalCategory P) :=
  p.mapCoefficients (predicateFunctor P).obj

/-- Ordered products and tagged sums have the chosen comparisons. -/
def component : (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) →
    (X : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔) →
    (predicateFunctor P).obj (p.eval.obj X) ≅
      (mapped P p).eval.obj (((predicateFunctor P).prod (predicateFunctor P)).obj X)
  | .term, _ => Iso.refl _
  | .formula, _ => Iso.refl _
  | .coefficient _, _ => Iso.refl _
  | .unit, _ => asIso (terminalComparison (predicateFunctor P))
  | .product a b, X =>
      asIso (prodComparison (predicateFunctor P) (a.eval.obj X) (b.eval.obj X)) ≪≫
        prod.mapIso (component a X) (component b X)
  | .sum a b, X =>
      (asIso (coprodComparison (predicateFunctor P) (a.eval.obj X) (b.eval.obj X))).symm ≪≫
        coprod.mapIso (component a X) (component b X)

theorem component_natural (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    {X Y : PredicateCategory 𝗣𝗔 × PredicateCategory 𝗣𝗔} (k : X ⟶ Y) :
    (predicateFunctor P).map (p.eval.map k) ≫ (component P p Y).hom =
      (component P p X).hom ≫
        (mapped P p).eval.map (((predicateFunctor P).prod (predicateFunctor P)).map k) := by
  induction p generalizing X Y with
  | term => simp [component,mapped,SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval]
  | formula => simp [component,mapped,SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval]
  | coefficient _ => simp [component,mapped,SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval]
  | unit => simp [component,mapped,SyntaxPolynomial.mapCoefficients,SyntaxPolynomial.eval]
  | product a b ia ib =>
      change (predicateFunctor P).map (prod.map _ _) ≫
        (prodComparison (predicateFunctor P) _ _ ≫ prod.map _ _) =
          (prodComparison (predicateFunctor P) _ _ ≫ prod.map _ _) ≫ prod.map _ _
      rw [← Category.assoc,prodComparison_natural,Category.assoc,prod.map_map,ia k,ib k]
      simp only [Category.assoc,prod.map_map]
  | sum a b ia ib =>
      change (predicateFunctor P).map (coprod.map _ _) ≫
        (inv (coprodComparison (predicateFunctor P) _ _) ≫ coprod.map _ _) =
          (inv (coprodComparison (predicateFunctor P) _ _) ≫ coprod.map _ _) ≫ coprod.map _ _
      apply (cancel_epi (coprodComparison (predicateFunctor P) (a.eval.obj X) (b.eval.obj X))).mp
      rw [← Category.assoc,coprodComparison_natural]
      simp only [Category.assoc,IsIso.hom_inv_id_assoc,coprod.map_map]
      rw [ia k,ib k]

def naturalIso (p : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) :
    p.eval ⋙ predicateFunctor P ≅
      ((predicateFunctor P).prod (predicateFunctor P)) ⋙ (mapped P p).eval :=
  NatIso.ofComponents (component P p) (fun k => component_natural P p k)

/-- The paired comparison retains both recursive sorts. -/
def jointIso (p q : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) :
    SyntaxPolynomial.jointFunctor p q ⋙ ((predicateFunctor P).prod (predicateFunctor P)) ≅
      ((predicateFunctor P).prod (predicateFunctor P)) ⋙
        SyntaxPolynomial.jointFunctor (mapped P p) (mapped P q) := by
  refine NatIso.ofComponents (fun X => ?_) ?_
  · exact {hom := ((component P p X).hom,(component P q X).hom)
           inv := ((component P p X).inv,(component P q X).inv)
           hom_inv_id := by ext <;> simp [SyntaxPolynomial.jointFunctor]
           inv_hom_id := by ext <;> simp [SyntaxPolynomial.jointFunctor]}
  · intro X Y k
    exact Prod.ext (component_natural P p k) (component_natural P q k)

/-- This constructs the algebra and does not infer its initiality from
an inclusion into a category with additional uniform morphisms. -/
def mappedAlgebra (p q : SyntaxPolynomial (PredicateCategory 𝗣𝗔))
    (A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor p q)) :
    Endofunctor.Algebra (SyntaxPolynomial.jointFunctor (mapped P p) (mapped P q)) where
  a := ((predicateFunctor P).prod (predicateFunctor P)).obj A.a
  str := (jointIso P p q).inv.app A.a ≫ ((predicateFunctor P).prod (predicateFunctor P)).map A.str

def wordAlgebra (p q : SyntaxPolynomial (PredicateCategory 𝗣𝗔)) :=
  mappedAlgebra P p q (sourceAlgebra p q)

end Polynomial
end CategoricalEssentialIncompleteness.V46.Miller.Syntax
