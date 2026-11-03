/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46CategoricalLists
import Mathlib.CategoryTheory.Products.Basic

/-! # The two-sorted syntax endofunctor and parameter-stable folds -/

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46

/-- Polynomial expressions in the term and formula sorts. -/
inductive SyntaxPolynomial (D : Type u) where
  | term
  | formula
  | coefficient (X : D)
  | unit
  | product (p q : SyntaxPolynomial D)
  | sum (p q : SyntaxPolynomial D)

namespace SyntaxPolynomial

variable {D : Type u} [Category.{v} D] [HasFiniteProducts D] [HasFiniteCoproducts D]

def productFunctor (F G : D × D ⥤ D) : D × D ⥤ D where
  obj X := F.obj X ⨯ G.obj X
  map f := prod.map (F.map f) (G.map f)
  map_id X := by simp
  map_comp f g := by rw [F.map_comp, G.map_comp, prod.map_map]

def sumFunctor (F G : D × D ⥤ D) : D × D ⥤ D where
  obj X := F.obj X ⨿ G.obj X
  map f := coprod.map (F.map f) (G.map f)
  map_id X := by simp
  map_comp f g := by rw [F.map_comp, G.map_comp, coprod.map_map]

/-- The action on morphisms uses the same product and coproduct maps
as the action on objects. -/
def eval : SyntaxPolynomial D → D × D ⥤ D
  | .term => CategoryTheory.Prod.fst D D
  | .formula => CategoryTheory.Prod.snd D D
  | .coefficient X => (Functor.const (D × D)).obj X
  | .unit => (Functor.const (D × D)).obj (⊤_ D)
  | .product p q => productFunctor p.eval q.eval
  | .sum p q => sumFunctor p.eval q.eval

/-- Powers are left associated, with power zero terminal and power one
the sort itself. In particular, the second power is a binary product. -/
def power (p : SyntaxPolynomial D) : ℕ → SyntaxPolynomial D
  | 0 => .unit
  | 1 => p
  | n + 2 => .product (power p (n + 1)) p

/-- The finite coproduct contains precisely the arities `0,…,d`. -/
def constructors (σ : ℕ → D) : ℕ → SyntaxPolynomial D
  | 0 => .product (.coefficient (σ 0)) (power .term 0)
  | n + 1 => .sum (constructors σ n)
      (.product (.coefficient (σ (n + 1))) (power .term (n + 1)))

def termExpression (V : D) (σ : ℕ → D) (d : ℕ) : SyntaxPolynomial D :=
  .sum (.coefficient V) (constructors σ d)

def formulaExpression (V : D) (π : ℕ → D) (d : ℕ) : SyntaxPolynomial D :=
  .sum (.sum (.sum (.sum (power .term 2) (constructors π d)) .formula)
    (power .formula 2)) (.product (.coefficient V) .formula)

@[simp] theorem eval_power_zero (p : SyntaxPolynomial D) (X : D × D) :
    (power p 0).eval.obj X = ⊤_ D := rfl

@[simp] theorem eval_power_one (p : SyntaxPolynomial D) (X : D × D) :
    (power p 1).eval.obj X = p.eval.obj X := rfl

@[simp] theorem eval_power_two (p : SyntaxPolynomial D) (X : D × D) :
    (power p 2).eval.obj X = (p.eval.obj X ⨯ p.eval.obj X) := rfl

def jointFunctor (p q : SyntaxPolynomial D) : D × D ⥤ D × D :=
  p.eval.prod' q.eval

end SyntaxPolynomial

section Parameters

variable {D : Type u} [Category.{v} D] [HasFiniteLimits D] [HasFiniteCoproducts D]

def constantUnitComparison (P : D) : ⊤_ (Over P) ⟶ constantFamily P (⊤_ D) :=
  Over.homMk (prod.lift (⊤_ (Over P)).hom
    (terminal.from (⊤_ (Over P)).left)) (by simp [constantFamily])

def constantProductComparison (P X Y : D) :
    constantFamily P X ⨯ constantFamily P Y ⟶ constantFamily P (X ⨯ Y) :=
  Over.homMk (prod.lift (constantFamily P X ⨯ constantFamily P Y).hom
    (prod.lift
      ((prod.fst : constantFamily P X ⨯ constantFamily P Y ⟶
        constantFamily P X).left ≫ prod.snd)
      ((prod.snd : constantFamily P X ⨯ constantFamily P Y ⟶
        constantFamily P Y).left ≫ prod.snd))) (by simp [constantFamily])

def constantCoproductComparison (P X Y : D) :
    constantFamily P X ⨿ constantFamily P Y ⟶ constantFamily P (X ⨿ Y) :=
  coprod.desc ((constantFamilyFunctor P).map coprod.inl)
    ((constantFamilyFunctor P).map coprod.inr)

namespace SyntaxPolynomial

/-- Replace each coefficient by its constant family, retaining the same
polynomial expression and using the products and coproducts of `D/P`. -/
def withParameters (P : D) : SyntaxPolynomial D → SyntaxPolynomial (Over P)
  | .term => .term
  | .formula => .formula
  | .coefficient X => .coefficient (constantFamily P X)
  | .unit => .unit
  | .product p q => .product (withParameters P p) (withParameters P q)
  | .sum p q => .sum (withParameters P p) (withParameters P q)

/-- The canonical morphism from the polynomial evaluated in the slice
to the constant family of its value in the base category. -/
def parameterComparison (P : D) (X : D × D) :
    (p : SyntaxPolynomial D) →
      (p.withParameters P).eval.obj (constantFamily P X.1, constantFamily P X.2) ⟶
        constantFamily P (p.eval.obj X)
  | .term => 𝟙 _
  | .formula => 𝟙 _
  | .coefficient _ => 𝟙 _
  | .unit => constantUnitComparison P
  | .product p q =>
      prod.map (parameterComparison P X p) (parameterComparison P X q) ≫
        constantProductComparison P (p.eval.obj X) (q.eval.obj X)
  | .sum p q =>
      coprod.map (parameterComparison P X p) (parameterComparison P X q) ≫
        constantCoproductComparison P (p.eval.obj X) (q.eval.obj X)

/-- Pull back both constructor morphisms of a two-sorted algebra. -/
def algebraWithParameters (p q : SyntaxPolynomial D)
    (A : Endofunctor.Algebra (jointFunctor p q)) (P : D) :
    Endofunctor.Algebra (jointFunctor (p.withParameters P) (q.withParameters P)) where
  a := (constantFamily P A.a.1, constantFamily P A.a.2)
  str := (parameterComparison P A.a p ≫ (constantFamilyFunctor P).map A.str.1,
    parameterComparison P A.a q ≫ (constantFamilyFunctor P).map A.str.2)

end SyntaxPolynomial

/-- Internal decidable equality of the variable object is given by the
pullback of the true injection along the equality test. -/
structure DecidableVariables (V : D) where
  test : V ⨯ V ⟶ (⊤_ D) ⨿ (⊤_ D)
  diagonal : IsPullback (prod.lift (𝟙 V) (𝟙 V)) (terminal.from V) test coprod.inr

/-- Definition A.1's syntax assumption, at arbitrary coefficients.
Only the coefficient objects with arity at most `d` occur in the functor. -/
structure CategoricalSyntax (V : D) (σ π : ℕ → D) (d : ℕ) where
  decidableVariables : DecidableVariables V
  algebra : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
    (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d))
  initial : IsInitial algebra
  stable : ∀ P : D, IsInitial (SyntaxPolynomial.algebraWithParameters
    (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)
      algebra P)
  lists : StableListAlgebra V

namespace CategoricalSyntax

variable {V : D} {σ π : ℕ → D} {d : ℕ} (S : CategoricalSyntax V σ π d)

def fold (B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
    (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d))) :
    S.algebra.a ⟶ B.a := (S.initial.to B).f

theorem fold_commutes (B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
    (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d))) :
    (SyntaxPolynomial.jointFunctor (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d)).map (S.fold B) ≫ B.str =
        S.algebra.str ≫ S.fold B :=
  (S.initial.to B).h

theorem fold_unique (B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
    (SyntaxPolynomial.termExpression V σ d) (SyntaxPolynomial.formulaExpression V π d)))
    (f : S.algebra.a ⟶ B.a)
    (hf : (SyntaxPolynomial.jointFunctor (SyntaxPolynomial.termExpression V σ d)
      (SyntaxPolynomial.formulaExpression V π d)).map f ≫ B.str = S.algebra.str ≫ f) :
    f = S.fold B :=
  congrArg Endofunctor.Algebra.Hom.f (S.initial.hom_ext ⟨f, hf⟩ (S.initial.to B))

/-- The target algebra in a parameter slice may have arbitrary carrier
families; it need not be a constant family. -/
def foldWithParameters (P : D)
    (B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
      ((SyntaxPolynomial.termExpression V σ d).withParameters P)
      ((SyntaxPolynomial.formulaExpression V π d).withParameters P))) :
    (constantFamily P S.algebra.a.1, constantFamily P S.algebra.a.2) ⟶ B.a :=
  ((S.stable P).to B).f

theorem foldWithParameters_commutes (P : D)
    (B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
      ((SyntaxPolynomial.termExpression V σ d).withParameters P)
      ((SyntaxPolynomial.formulaExpression V π d).withParameters P))) :
    (SyntaxPolynomial.jointFunctor
      ((SyntaxPolynomial.termExpression V σ d).withParameters P)
      ((SyntaxPolynomial.formulaExpression V π d).withParameters P)).map
        (S.foldWithParameters P B) ≫ B.str =
      (SyntaxPolynomial.algebraWithParameters (SyntaxPolynomial.termExpression V σ d)
        (SyntaxPolynomial.formulaExpression V π d) S.algebra P).str ≫
          S.foldWithParameters P B :=
  ((S.stable P).to B).h

theorem foldWithParameters_unique (P : D)
    (B : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor
      ((SyntaxPolynomial.termExpression V σ d).withParameters P)
      ((SyntaxPolynomial.formulaExpression V π d).withParameters P)))
    (f : (constantFamily P S.algebra.a.1, constantFamily P S.algebra.a.2) ⟶ B.a)
    (hf : (SyntaxPolynomial.jointFunctor
      ((SyntaxPolynomial.termExpression V σ d).withParameters P)
      ((SyntaxPolynomial.formulaExpression V π d).withParameters P)).map f ≫ B.str =
        (SyntaxPolynomial.algebraWithParameters (SyntaxPolynomial.termExpression V σ d)
          (SyntaxPolynomial.formulaExpression V π d) S.algebra P).str ≫ f) :
    f = S.foldWithParameters P B :=
  congrArg Endofunctor.Algebra.Hom.f ((S.stable P).hom_ext ⟨f, hf⟩ ((S.stable P).to B))

end CategoricalSyntax

end Parameters

end CategoricalEssentialIncompleteness.V46
