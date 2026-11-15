/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalSubstitutionIdentityParameters
public import CategoricalEssentialIncompleteness.V46SliceProductCoordinates

/-! # Reindexing polynomial algebras with specified constant carriers -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.ConstantParameterAlgebra
open SyntaxParameterChange
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]

/-- Algebra structure maps on specified constant carrier families. -/
structure Data (p q : SyntaxPolynomial D) (P : D) (X : D × D) where
  term : (p.withParameters P).eval.obj (constantFamily P X.1, constantFamily P X.2) ⟶
    constantFamily P X.1
  formula : (q.withParameters P).eval.obj (constantFamily P X.1, constantFamily P X.2) ⟶
    constantFamily P X.2

def Data.algebra {p q : SyntaxPolynomial D} {P : D} {X : D × D} (B : Data p q P X) :
    Endofunctor.Algebra
      (SyntaxPolynomial.jointFunctor (p.withParameters P) (q.withParameters P)) where
  a := (constantFamily P X.1, constantFamily P X.2)
  str := (B.term, B.formula)

variable {P Q : D} (r : P ⟶ Q)

/-- Retain the new parameter and compute the old algebra's value after
changing only its parameter coordinate. -/
def component (X : D × D) (p : SyntaxPolynomial D) {Y : D}
    (s : (p.withParameters Q).eval.obj (constantFamily Q X.1, constantFamily Q X.2) ⟶
      constantFamily Q Y) :
    (p.withParameters P).eval.obj (constantFamily P X.1, constantFamily P X.2) ⟶
      constantFamily P Y :=
  Over.homMk (prod.lift
    ((p.withParameters P).eval.obj (constantFamily P X.1, constantFamily P X.2)).hom
    ((polynomialMap r (baseMap r X.1, baseMap r X.2) p ≫ s).left ≫ prod.snd))
      (by simp [constantFamily])

@[reassoc] theorem component_commutes (X : D × D) (p : SyntaxPolynomial D) {Y : D}
    (s : (p.withParameters Q).eval.obj (constantFamily Q X.1, constantFamily Q X.2) ⟶
      constantFamily Q Y) :
    polynomialMap r (baseMap r X.1, baseMap r X.2) p ≫ s =
      (Over.map r).map (component r X p s) ≫ baseMap r Y := by
  apply constantFamily_hom_ext
  simp only [Over.comp_left, Over.map_map_left, component, Over.homMk_left, baseMap,
    Category.assoc, prod.map_snd, prod.lift_snd, Category.comp_id]

def Data.reindex {p q : SyntaxPolynomial D} {X : D × D} (B : Data p q Q X) :
    Data p q P X where
  term := component r X p B.term
  formula := component r X q B.formula

def pushHom {p q : SyntaxPolynomial D} {X : D × D} (B : Data p q Q X)
    {A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
      (p.withParameters P) (q.withParameters P))} (f : A ⟶ (B.reindex r).algebra) :
    ((Over.map r).obj A.a.1, (Over.map r).obj A.a.2) ⟶ B.algebra.a :=
  ((Over.map r).map f.f.1 ≫ baseMap r X.1, (Over.map r).map f.f.2 ≫ baseMap r X.2)

theorem pushHom_commutes {p q : SyntaxPolynomial D} {X : D × D} (B : Data p q Q X)
    {A : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
      (p.withParameters P) (q.withParameters P))} (f : A ⟶ (B.reindex r).algebra) :
    (polynomialMap r (pushHom r B f) p ≫ B.term,
      polynomialMap r (pushHom r B f) q ≫ B.formula) =
        ((Over.map r).map A.str.1 ≫ (pushHom r B f).1,
          (Over.map r).map A.str.2 ≫ (pushHom r B f).2) := by
  apply Prod.ext
  · change polynomialMap r
        ((((Over.map r).map f.f.1, (Over.map r).map f.f.2) :
          ((Over.map r).obj A.a.1, (Over.map r).obj A.a.2) ⟶
            ((Over.map r).obj (constantFamily P X.1),
              (Over.map r).obj (constantFamily P X.2))) ≫
          (baseMap r X.1, baseMap r X.2)) p ≫ B.term = _
    rw [← polynomialMap_left, Category.assoc, component_commutes,
      ← Category.assoc, ← (Over.map r).map_comp]
    have h : (p.withParameters P).eval.map f.f ≫ component r X p B.term =
        A.str.1 ≫ f.f.1 := congrArg Prod.fst f.h
    simpa only [Functor.map_comp, Category.assoc, pushHom] using
      congrArg (fun k => (Over.map r).map k ≫ baseMap r X.1) h
  · change polynomialMap r
        ((((Over.map r).map f.f.1, (Over.map r).map f.f.2) :
          ((Over.map r).obj A.a.1, (Over.map r).obj A.a.2) ⟶
            ((Over.map r).obj (constantFamily P X.1),
              (Over.map r).obj (constantFamily P X.2))) ≫
          (baseMap r X.1, baseMap r X.2)) q ≫ B.formula = _
    rw [← polynomialMap_left, Category.assoc, component_commutes,
      ← Category.assoc, ← (Over.map r).map_comp]
    have h : (q.withParameters P).eval.map f.f ≫ component r X q B.formula =
        A.str.2 ≫ f.f.2 := congrArg Prod.snd f.h
    simpa only [Functor.map_comp, Category.assoc, pushHom] using
      congrArg (fun k => (Over.map r).map k ≫ baseMap r X.2) h

/-- The reindexed fold compares to the original fold by the actual
changing-parameter algebra equation. -/
theorem fold_comparison {V : D} {σ π : ℕ → D} {n : ℕ}
    (S : CategoricalSyntax V σ π n) (X : D × D)
    (B : Data (SyntaxPolynomial.termExpression V σ n)
      (SyntaxPolynomial.formulaExpression V π n) Q X) :
    pushHom r B ((S.stable P).to (B.reindex r).algebra) =
      S.crossParameterFold r B.algebra :=
  S.crossParameterFold_unique r B.algebra
    (pushHom r B ((S.stable P).to (B.reindex r).algebra))
    (pushHom_commutes r B ((S.stable P).to (B.reindex r).algebra))

end CategoricalEssentialIncompleteness.V46.ConstantParameterAlgebra
