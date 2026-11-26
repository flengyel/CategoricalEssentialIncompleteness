/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46ForkFormulaParameterComponents

/-! # Uniqueness of formula folds across arbitrary parameter morphisms -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ForkFormulaParameterChange
open ForkFirstOrderFormula ForkFormulaParameterComponents
local instance (X : C) : Regular (Over X) := RegularSlices.regular X

/-- The variable object has label `false` and the propositional atoms have label `true`. -/
def template : SyntaxPolynomial Bool :=
  .sum (.sum (.sum (.sum (.product (.coefficient false) (.coefficient false))
    (.coefficient true)) .formula) (.product .formula .formula))
      (.product (.coefficient false) .formula)

def coefficient (N D P : C) (t : Bool) : Over P := constantFamily P (if t then D else N)

def coefficientMap (N : C) {D E P Q : C} (b : P ⟶ Q) (h : D ⟶ E) (t : Bool) :
    (Over.map b).obj (coefficient N D P t) ⟶ coefficient N E Q t :=
  match t with
  | false => Over.homMk (prod.map b (𝟙 N)) (by simp [coefficient, constantFamily])
  | true => Over.homMk (prod.map b h) (by simp [coefficient, constantFamily])

/-- Postcomposition has a forward comparison of relative polynomials.
An atom transition may identify labels, and b is arbitrary. -/
def comparison (N : C) {D E P Q : C} (b : P ⟶ Q) (h : D ⟶ E) :
    polynomial N D P ⋙ Over.map b ⟶ Over.map b ⋙ polynomial N E Q where
  app X := LaxPolynomialComparison.component (Over.map b) (coefficientMap N b h)
    template (⊤_ (Over P), X)
  naturality {X Y} f := by
    have hn := LaxPolynomialComparison.naturality (Over.map b)
      (coefficientMap N b h) template (X := (⊤_ (Over P), X))
        (Y := (⊤_ (Over P), Y)) (𝟙 _, f)
    exact hn

def fold (N : C) {D E P Q : C} (b : P ⟶ Q) (h : D ⟶ E)
    (B : Endofunctor.Algebra (polynomial N E Q)) :
    (Over.map b).obj (algebra N D P).a ⟶ B.a :=
  LaxAlgebraAdjunction.fold (Over.mapPullbackAdj b) (comparison N b h)
    (algebra N D P) (initial N D P) B

theorem fold_over (N : C) {D E P Q : C} (b : P ⟶ Q) (h : D ⟶ E)
    (B : Endofunctor.Algebra (polynomial N E Q)) :
    (fold N b h B).left ≫ B.a.hom = (algebra N D P).a.hom ≫ b := Over.w _

theorem fold_constructor (N : C) {D E P Q : C} (b : P ⟶ Q) (h : D ⟶ E)
    (B : Endofunctor.Algebra (polynomial N E Q)) :
    (comparison N b h).app (algebra N D P).a ≫
      (polynomial N E Q).map (fold N b h B) ≫ B.str =
        (Over.map b).map (algebra N D P).str ≫ fold N b h B :=
  LaxAlgebraAdjunction.fold_constructor _ _ _ _ _

/-- The comparison constructs the reindexed target algebra via the
pullback adjunction. Neither initiality nor target evaluation is assumed. -/
theorem unique (N : C) {D E P Q : C} (b : P ⟶ Q) (h : D ⟶ E)
    (B : Endofunctor.Algebra (polynomial N E Q))
    (f g : (Over.map b).obj (algebra N D P).a ⟶ B.a)
    (hf : (comparison N b h).app (algebra N D P).a ≫ (polynomial N E Q).map f ≫ B.str =
      (Over.map b).map (algebra N D P).str ≫ f)
    (hg : (comparison N b h).app (algebra N D P).a ≫ (polynomial N E Q).map g ≫ B.str =
      (Over.map b).map (algebra N D P).str ≫ g) : f = g :=
  LaxAlgebraAdjunction.unique (Over.mapPullbackAdj b) (comparison N b h)
    (algebra N D P) (initial N D P) B f g hf hg
/-- Uniqueness also applies to raw carrier morphisms with the projection
and constructor equations, so the quantified maps need no chosen presentation. -/
theorem underlying_unique (N : C) {D E P Q : C} (b : P ⟶ Q) (h : D ⟶ E)
    (B : Endofunctor.Algebra (polynomial N E Q))
    (f g : (algebra N D P).a.left ⟶ B.a.left)
    (hfP : f ≫ B.a.hom = (algebra N D P).a.hom ≫ b)
    (hgP : g ≫ B.a.hom = (algebra N D P).a.hom ≫ b)
    (hf : (comparison N b h).app (algebra N D P).a ≫
      (polynomial N E Q).map (Over.homMk f hfP) ≫ B.str =
        (Over.map b).map (algebra N D P).str ≫ Over.homMk f hfP)
    (hg : (comparison N b h).app (algebra N D P).a ≫
      (polynomial N E Q).map (Over.homMk g hgP) ≫ B.str =
        (Over.map b).map (algebra N D P).str ≫ Over.homMk g hgP) : f = g :=
  congrArg Over.Hom.left (unique N b h B (Over.homMk f hfP) (Over.homMk g hgP) hf hg)
end CategoricalEssentialIncompleteness.V46.ForkFormulaParameterChange
