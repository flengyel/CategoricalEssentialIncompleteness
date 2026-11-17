/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46ForkCanonicalFormulaStability

/-! # Assembling initial two-sorted slice algebras from their evaluations -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v u' v' w
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ProductAdjunction
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
variable {L : C ⥤ D} {R : D ⥤ C}

def square (adj : L ⊣ R) : L.prod L ⊣ R.prod R :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun X Y => Equiv.prodCongr (adj.homEquiv X.1 Y.1) (adj.homEquiv X.2 Y.2)
    homEquiv_naturality_left_symm := fun f g => Prod.ext
      (adj.homEquiv_naturality_left_symm f.1 g.1)
      (adj.homEquiv_naturality_left_symm f.2 g.2)
    homEquiv_naturality_right := fun f g => Prod.ext
      (adj.homEquiv_naturality_right f.1 g.1)
      (adj.homEquiv_naturality_right f.2 g.2) }
end CategoricalEssentialIncompleteness.V46.ProductAdjunction

namespace CategoricalEssentialIncompleteness.V46.SliceAlgebraInitiality
variable {J : Type u} [Category.{v} J] {C : Type u'} [Category.{v'} C]
variable [HasFiniteLimits C] [HasFiniteCoproducts C] {I : Type w}
variable (c : I → J ⥤ C) (P : J ⥤ C) (p q : SyntaxPolynomial I)

abbrev polynomial := SyntaxPolynomial.jointFunctor
  (p.mapCoefficients (SlicePolynomialComparison.globalCoefficients c P))
  (q.mapCoefficients (SlicePolynomialComparison.globalCoefficients c P))
abbrev localPolynomial (j : J) := SyntaxPolynomial.jointFunctor
  (p.mapCoefficients (SlicePolynomialComparison.localCoefficients c P j))
  (q.mapCoefficients (SlicePolynomialComparison.localCoefficients c P j))
abbrev evaluation (j : J) :=
  (SliceEvaluation.componentFunctor P j).prod (SliceEvaluation.componentFunctor P j)
abbrev component (B : Endofunctor.Algebra (polynomial c P p q)) (j : J) :=
  AlgebraEvaluation.algebra (evaluation P j) (SlicePolynomialComparison.jointIso c P p q j) B

def comparison {j k : J} (f : j ⟶ k) :
    localPolynomial c P p q j ⋙ (Over.map (P.map f)).prod (Over.map (P.map f)) ⟶
      (Over.map (P.map f)).prod (Over.map (P.map f)) ⋙ localPolynomial c P p q k where
  app X := (LaxPolynomialComparison.component (Over.map (P.map f))
    (fun i => SliceEvaluation.coefficientTransition P (c i) f) p X,
      LaxPolynomialComparison.component (Over.map (P.map f))
        (fun i => SliceEvaluation.coefficientTransition P (c i) f) q X)
  naturality {_ _} m := Prod.ext
    (LaxPolynomialComparison.naturality (Over.map (P.map f))
      (fun i => SliceEvaluation.coefficientTransition P (c i) f) p m)
    (LaxPolynomialComparison.naturality (Over.map (P.map f))
      (fun i => SliceEvaluation.coefficientTransition P (c i) f) q m)

abbrev transition (X : Over P × Over P) {j k : J} (f : j ⟶ k) :
    ((Over.map (P.map f)).prod (Over.map (P.map f))).obj ((evaluation P j).obj X) ⟶
      (evaluation P k).obj X :=
  (SliceEvaluation.transition P X.1 f, SliceEvaluation.transition P X.2 f)

theorem transition_constructor (B : Endofunctor.Algebra (polynomial c P p q))
    {j k : J} (f : j ⟶ k) :
    (comparison c P p q f).app (component c P p q B j).a ≫
        (localPolynomial c P p q k).map (transition P B.a f) ≫ (component c P p q B k).str =
      ((Over.map (P.map f)).prod (Over.map (P.map f))).map (component c P p q B j).str ≫
        transition P B.a f := by
  apply Prod.ext
  · change LaxPolynomialComparison.component (Over.map (P.map f))
      (fun i => SliceEvaluation.coefficientTransition P (c i) f) p
        (SlicePolynomialComparison.localCarrier P B.a j) ≫
      (p.mapCoefficients (SlicePolynomialComparison.localCoefficients c P k)).eval.map
        (SliceEvaluation.transition P B.a.1 f, SliceEvaluation.transition P B.a.2 f) ≫
        SlicePolynomialComparison.operation c P p B.a B.a.1 B.str.1 k =
      (Over.map (P.map f)).map (SlicePolynomialComparison.operation c P p B.a B.a.1 B.str.1 j) ≫ _
    simpa only [SlicePolynomialComparison.input, LaxPolynomialComparison.input,
      Category.assoc] using SlicePolynomialComparison.operation_square c P p B.a B.a.1 B.str.1 f
  · change LaxPolynomialComparison.component (Over.map (P.map f))
      (fun i => SliceEvaluation.coefficientTransition P (c i) f) q
        (SlicePolynomialComparison.localCarrier P B.a j) ≫
      (q.mapCoefficients (SlicePolynomialComparison.localCoefficients c P k)).eval.map
        (SliceEvaluation.transition P B.a.1 f, SliceEvaluation.transition P B.a.2 f) ≫
        SlicePolynomialComparison.operation c P q B.a B.a.2 B.str.2 k =
      (Over.map (P.map f)).map (SlicePolynomialComparison.operation c P q B.a B.a.2 B.str.2 j) ≫ _
    simpa only [SlicePolynomialComparison.input, LaxPolynomialComparison.input,
      Category.assoc] using SlicePolynomialComparison.operation_square c P q B.a B.a.2 B.str.2 f

variable (A : Endofunctor.Algebra (polynomial c P p q))
variable (hA : ∀ j, IsInitial (component c P p q A j))

abbrev foldComponent (B : Endofunctor.Algebra (polynomial c P p q)) (j : J) :=
  (hA j).to (component c P p q B j)

theorem fold_natural (B : Endofunctor.Algebra (polynomial c P p q))
    {j k : J} (f : j ⟶ k) :
    transition P A.a f ≫ (foldComponent c P p q A hA B k).f =
      ((Over.map (P.map f)).prod (Over.map (P.map f))).map
        (foldComponent c P p q A hA B j).f ≫ transition P B.a f :=
  LaxAlgebraAdjunction.fold_natural (ProductAdjunction.square (Over.mapPullbackAdj (P.map f)))
    (comparison c P p q f) (component c P p q A j) (component c P p q B j) (hA j)
    (component c P p q A k) (component c P p q B k) (transition P A.a f) (transition P B.a f)
    (transition_constructor c P p q A f) (transition_constructor c P p q B f)
    (foldComponent c P p q A hA B j) (foldComponent c P p q A hA B k)

def foldMap (B : Endofunctor.Algebra (polynomial c P p q)) : A.a ⟶ B.a :=
  (Over.homMk {
    app j := (foldComponent c P p q A hA B j).f.1.left
    naturality {j k} f := congrArg (fun m => m.1.left) (fold_natural c P p q A hA B f) }
      (by ext j; exact Over.w (foldComponent c P p q A hA B j).f.1),
    Over.homMk {
      app j := (foldComponent c P p q A hA B j).f.2.left
      naturality {j k} f := congrArg (fun m => m.2.left) (fold_natural c P p q A hA B f) }
      (by ext j; exact Over.w (foldComponent c P p q A hA B j).f.2))

theorem fold_constructor (B : Endofunctor.Algebra (polynomial c P p q)) :
    (polynomial c P p q).map (foldMap c P p q A hA B) ≫ B.str =
      A.str ≫ foldMap c P p q A hA B := by
  apply Prod.ext
  · apply Over.OverMorphism.ext
    apply NatTrans.ext
    funext j
    exact congrArg (fun m => m.1.left)
      ((AlgebraEvaluation.hom_condition_iff (evaluation P j)
        (SlicePolynomialComparison.jointIso c P p q j) A B
          (foldMap c P p q A hA B)).mp (by exact (foldComponent c P p q A hA B j).h))
  · apply Over.OverMorphism.ext
    apply NatTrans.ext
    funext j
    exact congrArg (fun m => m.2.left)
      ((AlgebraEvaluation.hom_condition_iff (evaluation P j)
        (SlicePolynomialComparison.jointIso c P p q j) A B
          (foldMap c P p q A hA B)).mp (by exact (foldComponent c P p q A hA B j).h))

def fold (B : Endofunctor.Algebra (polynomial c P p q)) : A ⟶ B :=
  ⟨foldMap c P p q A hA B, fold_constructor c P p q A hA B⟩

/-- Local initiality supplies natural global folds, and global uniqueness
ranges over all pairs of underlying morphisms over the parameter. -/
def initial : IsInitial A :=
  IsInitial.ofUniqueHom (fold c P p q A hA) (by
    intro B m
    have h (j : J) : (evaluation P j).map m.f = (foldComponent c P p q A hA B j).f :=
      congrArg Endofunctor.Algebra.Hom.f ((hA j).hom_ext
        (⟨(evaluation P j).map m.f,
          (AlgebraEvaluation.hom_condition_iff (evaluation P j)
            (SlicePolynomialComparison.jointIso c P p q j) A B m.f).mpr
              (congrArg (evaluation P j).map m.h)⟩ :
          component c P p q A j ⟶ component c P p q B j) _)
    apply Endofunctor.Algebra.Hom.ext
    apply Prod.ext
    · apply Over.OverMorphism.ext
      exact NatTrans.ext (funext (fun j => congrArg (fun n => n.1.left) (h j)))
    · apply Over.OverMorphism.ext
      exact NatTrans.ext (funext (fun j => congrArg (fun n => n.2.left) (h j))))
end CategoricalEssentialIncompleteness.V46.SliceAlgebraInitiality
