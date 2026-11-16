/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46NumericalDiagramSyntax
public import Mathlib.Tactic.IrreducibleDef
public import CategoricalEssentialIncompleteness.V46ForkDerivationDiagram

/-! # First-order formula initiality with arbitrary fork atom labels -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkFirstOrderFormula
abbrev C := NumericalTuples.Object
abbrev Object := WalkingSpan ⥤ C

/-- A one-sorted expression: equality, atoms, negation, implication and
universal quantification. Recursive occurrences use the formula sort only. -/
def expression (N D : C) : SyntaxPolynomial C :=
  .sum (.sum (.sum (.sum (.product (.coefficient N) (.coefficient N))
    (.coefficient D)) .formula) (.product .formula .formula))
      (.product (.coefficient N) .formula)

def insert : C ⥤ C × C := ((Functor.const C).obj (⊤_ C)).prod' (𝟭 C)

def polynomial (N D : C) : C ⥤ C := insert ⋙ (expression N D).eval

/-- The equation is retained while the numerical construction is hidden
from incidental kernel reduction through its carrier projections. -/
irreducible_def pairAlgebra (N D : C) :
    Endofunctor.Algebra (SyntaxPolynomial.jointFunctor .unit (expression N D)) :=
  (NumericalSyntax.data .unit (expression N D)).1

def pairInitial (N D : C) : IsInitial (pairAlgebra N D) := by
  rw [pairAlgebra_def]
  exact (NumericalSyntax.data .unit (expression N D)).2.1

def pairStable (N D P : C) : IsInitial
    (SyntaxPolynomial.algebraWithParameters .unit (expression N D) (pairAlgebra N D) P) := by
  rw [pairAlgebra_def]
  exact (NumericalSyntax.data .unit (expression N D)).2.2 P

def componentAlgebra (N D : C) : Endofunctor.Algebra (polynomial N D) :=
  ⟨(pairAlgebra N D).a.2, (pairAlgebra N D).str.2⟩

def targetPair {N D : C} (B : Endofunctor.Algebra (polynomial N D)) :
    Endofunctor.Algebra (SyntaxPolynomial.jointFunctor .unit (expression N D)) :=
  ⟨(⊤_ C, B.a), (terminal.from _, B.str)⟩

def componentFold {N D : C} (B : Endofunctor.Algebra (polynomial N D)) :
    componentAlgebra N D ⟶ B where
  f := ((pairInitial N D).to (targetPair B)).f.2
  h := congrArg Prod.snd (((pairInitial N D).to
    (targetPair B)).h)

def componentInitial (N D : C) : IsInitial (componentAlgebra N D) :=
  IsInitial.ofUniqueHom componentFold (by
    intro B m
    apply Endofunctor.Algebra.Hom.ext
    let t : pairAlgebra N D ⟶ targetPair B := {
      f := (terminal.from _, m.f)
      h := Prod.ext (terminalIsTerminal.hom_ext _ _) m.h }
    exact congrArg (fun k => k.f.2) ((pairInitial N D).hom_ext
      t ((pairInitial N D).to (targetPair B))))

/-- The numerical variables are all natural numbers, at every component. -/
def numbers : Object := (Functor.const WalkingSpan).obj
  (NumericalTuples.unary (⟨EffectiveFork.natCarrier⟩ : EnumerableCarriers.Total))

/-- Coefficient transitions act on atoms; variables are retained. -/
def transition {D E : C} (h : D ⟶ E) (N : C) : polynomial N D ⟶ polynomial N E where
  app X := coprod.map (coprod.map (coprod.map (coprod.map (𝟙 _) h) (𝟙 X))
    (𝟙 (X ⨯ X))) (𝟙 (N ⨯ X))
  naturality {_ _} f := by
    dsimp [polynomial, insert, expression, SyntaxPolynomial.eval,
      SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor]
    simp only [coprod.map_map, Category.id_comp, Category.comp_id]

variable (D : Object)

def polynomialDiagram : WalkingSpan ⥤ (C ⥤ C) where
  obj j := polynomial (numbers.obj j) (D.obj j)
  map f := transition (D.map f) (numbers.obj _)
  map_id j := by
    ext X
    simp only [D.map_id]
    change coprod.map (coprod.map (coprod.map (coprod.map (𝟙 _) (𝟙 _)) (𝟙 _))
      (𝟙 _)) (𝟙 _) = 𝟙 _
    simp only [coprod.map_id_id]
  map_comp f g := by
    ext X
    change coprod.map (coprod.map (coprod.map (coprod.map (𝟙 _) (D.map (f ≫ g))) (𝟙 _))
      (𝟙 _)) (𝟙 _) = _
    rw [D.map_comp]
    dsimp [transition, polynomial, insert, expression, SyntaxPolynomial.eval,
      SyntaxPolynomial.sumFunctor, SyntaxPolynomial.productFunctor, numbers]
    simp only [coprod.map_map, Category.id_comp]

def algebra : Endofunctor.Algebra (DiagramInitialAlgebras.diagonal (polynomialDiagram D)) :=
  DiagramInitialAlgebras.algebra (polynomialDiagram D)
    (fun j => componentAlgebra (numbers.obj j) (D.obj j))
    (fun j => componentInitial (numbers.obj j) (D.obj j))

def initial : IsInitial (algebra D) :=
  DiagramInitialAlgebras.initial (polynomialDiagram D)
    (fun j => componentAlgebra (numbers.obj j) (D.obj j))
    (fun j => componentInitial (numbers.obj j) (D.obj j))

/-- The displayed five summands are the actual object part of Q_D. -/
theorem polynomial_object (Y : Object) (j : WalkingSpan) :
    ((DiagramInitialAlgebras.diagonal (polynomialDiagram D)).obj Y).obj j =
      (((((numbers.obj j ⨯ numbers.obj j) ⨿ D.obj j) ⨿ Y.obj j) ⨿
        (Y.obj j ⨯ Y.obj j)) ⨿ (numbers.obj j ⨯ Y.obj j)) := rfl

@[simp] theorem numbers_full (j : WalkingSpan) : (numbers.obj j).support = Set.univ := rfl

@[simp] theorem numbers_transition {j k : WalkingSpan} (f : j ⟶ k) :
    numbers.map f = 𝟙 (numbers.obj j) := rfl

theorem polynomial_transition (Y : Object) {j k : WalkingSpan} (f : j ⟶ k) :
    ((DiagramInitialAlgebras.diagonal (polynomialDiagram D)).obj Y).map f =
      coprod.map (coprod.map (coprod.map (coprod.map (𝟙 _) (D.map f)) (Y.map f))
        (prod.map (Y.map f) (Y.map f))) (prod.map (𝟙 (numbers.obj j)) (Y.map f)) := by
  dsimp [DiagramInitialAlgebras.diagonal, polynomialDiagram, polynomial, insert,
    expression, transition, SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor,
    SyntaxPolynomial.productFunctor]
  simp only [coprod.map_map, Category.id_comp, Category.comp_id, prod.map_id_id]

def fold (B : Endofunctor.Algebra (DiagramInitialAlgebras.diagonal (polynomialDiagram D))) :
    algebra D ⟶ B := (initial D).to B

theorem fold_constructor
    (B : Endofunctor.Algebra (DiagramInitialAlgebras.diagonal (polynomialDiagram D))) :
    (DiagramInitialAlgebras.diagonal (polynomialDiagram D)).map (fold D B).f ≫ B.str =
      (algebra D).str ≫ (fold D B).f := (fold D B).h

theorem fold_natural
    (B : Endofunctor.Algebra (DiagramInitialAlgebras.diagonal (polynomialDiagram D)))
    {j k : WalkingSpan} (f : j ⟶ k) :
    (algebra D).a.map f ≫ (fold D B).f.app k =
      (fold D B).f.app j ≫ B.a.map f := (fold D B).f.naturality f

theorem fold_unique
    (B : Endofunctor.Algebra (DiagramInitialAlgebras.diagonal (polynomialDiagram D)))
    (m : algebra D ⟶ B) : m = fold D B := (initial D).hom_ext _ _

theorem fold_underlying_unique
    (B : Endofunctor.Algebra (DiagramInitialAlgebras.diagonal (polynomialDiagram D)))
    (m : (algebra D).a ⟶ B.a)
    (hm : (DiagramInitialAlgebras.diagonal (polynomialDiagram D)).map m ≫ B.str =
      (algebra D).str ≫ m) : m = (fold D B).f :=
  congrArg Endofunctor.Algebra.Hom.f ((initial D).hom_ext (⟨m, hm⟩ : algebra D ⟶ B) _)

end CategoricalEssentialIncompleteness.V46.ForkFirstOrderFormula
