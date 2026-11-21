/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46SliceEvaluation
public import CategoricalEssentialIncompleteness.V46LaxPolynomialCoherence

/-! # Canonical polynomial comparison for arbitrary slice families -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v u' v' w
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.SlicePolynomialComparison
variable {J : Type u} [Category.{v} J] {C : Type u'} [Category.{v'} C]
variable [HasFiniteLimits C] [HasFiniteCoproducts C] {I : Type w}
variable (c : I → J ⥤ C) (P : J ⥤ C)

abbrev globalCoefficients (i : I) : Over P := constantFamily P (c i)
abbrev localCoefficients (j : J) (i : I) : Over (P.obj j) :=
  constantFamily (P.obj j) ((c i).obj j)

abbrev localCarrier (X : Over P × Over P) (j : J) : Over (P.obj j) × Over (P.obj j) :=
  ((SliceEvaluation.componentFunctor P j).obj X.1,
    (SliceEvaluation.componentFunctor P j).obj X.2)

def component (p : SyntaxPolynomial I) (X : Over P × Over P) (j : J) :
    (SliceEvaluation.componentFunctor P j).obj
        ((p.mapCoefficients (globalCoefficients c P)).eval.obj X) ⟶
      (p.mapCoefficients (localCoefficients c P j)).eval.obj (localCarrier P X j) :=
  LaxPolynomialComparison.component (SliceEvaluation.componentFunctor P j)
    (fun i => (SliceEvaluation.coefficientIso P (c i) j).hom) p X

instance component_isIso (p : SyntaxPolynomial I) (X : Over P × Over P) (j : J) :
    IsIso (component c P p X j) := by
  exact LaxPolynomialComparison.component_isIso (SliceEvaluation.componentFunctor P j)
    (fun i => (SliceEvaluation.coefficientIso P (c i) j).hom) p X

/-- The comparison includes both recursive sorts and arbitrary target
families. Evaluation's product preservation is proved in `SliceEvaluation`. -/
def jointIso (p q : SyntaxPolynomial I) (j : J) :
    SyntaxPolynomial.jointFunctor (p.mapCoefficients (globalCoefficients c P))
        (q.mapCoefficients (globalCoefficients c P)) ⋙
        (SliceEvaluation.componentFunctor P j).prod (SliceEvaluation.componentFunctor P j) ≅
      ((SliceEvaluation.componentFunctor P j).prod (SliceEvaluation.componentFunctor P j)) ⋙
        SyntaxPolynomial.jointFunctor (p.mapCoefficients (localCoefficients c P j))
          (q.mapCoefficients (localCoefficients c P j)) :=
  NatIso.ofComponents (fun X => Iso.prod (asIso (component c P p X j))
    (asIso (component c P q X j))) (by
      intro X Y m
      exact Prod.ext
        (LaxPolynomialComparison.naturality (SliceEvaluation.componentFunctor P j)
          (fun i => (SliceEvaluation.coefficientIso P (c i) j).hom) p m)
        (LaxPolynomialComparison.naturality (SliceEvaluation.componentFunctor P j)
          (fun i => (SliceEvaluation.coefficientIso P (c i) j).hom) q m))

omit [HasFiniteCoproducts C] in
/-- This is the exact expression used by `algebraWithParameters`, with
its labelled coefficient positions retained. -/
theorem withParameters_eq (p : SyntaxPolynomial I) :
    (p.mapCoefficients c).withParameters P =
      p.mapCoefficients (globalCoefficients c P) := by
  induction p with
  | term => rfl
  | formula => rfl
  | coefficient => rfl
  | unit => rfl
  | product p q hp hq => simp only [SyntaxPolynomial.mapCoefficients,
      SyntaxPolynomial.withParameters, hp, hq]
  | sum p q hp hq => simp only [SyntaxPolynomial.mapCoefficients,
      SyntaxPolynomial.withParameters, hp, hq]

/-- The component polynomial input along a parameter transition. There
is no assumption that postcomposition preserves relative products. -/
def input (p : SyntaxPolynomial I) (X : Over P × Over P) {j k : J} (f : j ⟶ k) :
    (Over.map (P.map f)).obj
        ((p.mapCoefficients (localCoefficients c P j)).eval.obj (localCarrier P X j)) ⟶
      (p.mapCoefficients (localCoefficients c P k)).eval.obj (localCarrier P X k) :=
  LaxPolynomialComparison.input (Over.map (P.map f))
    (fun i => SliceEvaluation.coefficientTransition P (c i) f) p
    (localCarrier P X j) (localCarrier P X k)
    (SliceEvaluation.transition P X.1 f, SliceEvaluation.transition P X.2 f)

/-- The evaluation and coefficient comparisons commute with every parameter transition,
for arbitrary recursive families. -/
theorem transition_square (p : SyntaxPolynomial I) (X : Over P × Over P)
    {j k : J} (f : j ⟶ k) :
    SliceEvaluation.transition P ((p.mapCoefficients (globalCoefficients c P)).eval.obj X) f ≫
        component c P p X k =
      (Over.map (P.map f)).map (component c P p X j) ≫ input c P p X f :=
  LaxPolynomialComparison.natural_square (SliceEvaluation.componentFunctor P j)
    (fun i => (SliceEvaluation.coefficientIso P (c i) j).hom)
    (SliceEvaluation.componentFunctor P k) (Over.map (P.map f))
    (fun i => (SliceEvaluation.coefficientIso P (c i) k).hom)
    (fun i => SliceEvaluation.coefficientTransition P (c i) f)
    (Over.postMap (X := P) ((evaluation J C).map f))
    (fun i => SliceEvaluation.coefficient_square P (c i) f) p X

/-- Every global polynomial operation induces a component operation, using the inverse of
the proved evaluation comparison. -/
def operation (p : SyntaxPolynomial I) (X : Over P × Over P) (Y : Over P)
    (r : (p.mapCoefficients (globalCoefficients c P)).eval.obj X ⟶ Y) (j : J) :
    (p.mapCoefficients (localCoefficients c P j)).eval.obj (localCarrier P X j) ⟶
      (SliceEvaluation.componentFunctor P j).obj Y :=
  inv (component c P p X j) ≫ (SliceEvaluation.componentFunctor P j).map r

/-- Naturality of a target operation is derived from its global morphism;
the constructor square is not an additional input. -/
theorem operation_square (p : SyntaxPolynomial I) (X : Over P × Over P) (Y : Over P)
    (r : (p.mapCoefficients (globalCoefficients c P)).eval.obj X ⟶ Y)
    {j k : J} (f : j ⟶ k) :
    input c P p X f ≫ operation c P p X Y r k =
      (Over.map (P.map f)).map (operation c P p X Y r j) ≫ SliceEvaluation.transition P Y f := by
  apply (cancel_epi ((Over.map (P.map f)).map (component c P p X j))).mp
  dsimp only [operation]
  rw [← Category.assoc, ← transition_square c P p X f,
    Category.assoc, IsIso.hom_inv_id_assoc]
  simp only [Functor.map_comp, Functor.map_inv, Category.assoc, IsIso.hom_inv_id_assoc]
  exact ((Over.postMap (X := P) ((evaluation J C).map f)).naturality r).symm

end CategoricalEssentialIncompleteness.V46.SlicePolynomialComparison
