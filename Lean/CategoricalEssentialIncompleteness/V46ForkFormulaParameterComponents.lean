/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46ForkFirstOrderFormula
public import CategoricalEssentialIncompleteness.V46RegularSlices
public import CategoricalEssentialIncompleteness.V46LaxAlgebraAdjunction
public import CategoricalEssentialIncompleteness.V46LaxPolynomialComparison

/-! # Formula folds with arbitrary parameter families and parameter morphisms -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ForkFormulaParameterComponents
open ForkFirstOrderFormula
variable (N D P : C)
local instance (X : C) : Regular (Over X) := RegularSlices.regular X

/-- The two-sort parameter algebra already has initiality for arbitrary target families.
Its unused first sort is retained here. -/
def pairAlgebra := SyntaxPolynomial.algebraWithParameters .unit (expression N D)
  (ForkFirstOrderFormula.pairAlgebra N D) P

def insert (P : C) : Over P ⥤ Over P × Over P :=
  ((Functor.const (Over P)).obj (⊤_ (Over P))).prod' (𝟭 (Over P))

def polynomial : Over P ⥤ Over P :=
  insert P ⋙ ((expression N D).withParameters P).eval

def algebra : Endofunctor.Algebra (polynomial N D P) :=
  ⟨constantFamily P (componentAlgebra N D).a, (pairAlgebra N D P).str.2⟩

def targetPair (B : Endofunctor.Algebra (polynomial N D P)) :
    Endofunctor.Algebra (SyntaxPolynomial.jointFunctor .unit
      ((expression N D).withParameters P)) :=
  ⟨(⊤_ (Over P), B.a), (terminal.from _, B.str)⟩

def fold (B : Endofunctor.Algebra (polynomial N D P)) : algebra N D P ⟶ B where
  f := ((ForkFirstOrderFormula.pairStable N D P).to (targetPair N D P B)).f.2
  h := congrArg Prod.snd (((ForkFirstOrderFormula.pairStable N D P).to
    (targetPair N D P B)).h)

/-- The target carrier is any object over P, not merely a constant family. -/
def initial : IsInitial (algebra N D P) :=
  IsInitial.ofUniqueHom (fold N D P) (by
    intro B m
    apply Endofunctor.Algebra.Hom.ext
    let t : pairAlgebra N D P ⟶ targetPair N D P B := {
      f := (terminal.from _, m.f)
      h := Prod.ext (terminalIsTerminal.hom_ext _ _) m.h }
    exact congrArg (fun k => k.f.2) ((ForkFirstOrderFormula.pairStable N D P).hom_ext
      t ((ForkFirstOrderFormula.pairStable N D P).to (targetPair N D P B))))

theorem fold_over (B : Endofunctor.Algebra (polynomial N D P)) :
    (fold N D P B).f.left ≫ B.a.hom = (constantFamily P (componentAlgebra N D).a).hom :=
  Over.w _

theorem fold_constructor (B : Endofunctor.Algebra (polynomial N D P)) :
    (polynomial N D P).map (fold N D P B).f ≫ B.str =
      (algebra N D P).str ≫ (fold N D P B).f := (fold N D P B).h

theorem fold_unique (B : Endofunctor.Algebra (polynomial N D P)) (m : algebra N D P ⟶ B) :
    m = fold N D P B := (initial N D P).hom_ext _ _

end CategoricalEssentialIncompleteness.V46.ForkFormulaParameterComponents
