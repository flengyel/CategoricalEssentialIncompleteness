/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46SlicePolynomialComparison
public import CategoricalEssentialIncompleteness.V46ForkParameterizedFormulaFolds

/-! # Natural folds into parameterized formula algebras -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ForkCanonicalParameterTargets
open ForkFirstOrderFormula
variable (D P : Object)

abbrev coefficients (t : Bool) : Object := if t then D else numbers

def insert : Over P ⥤ Over P × Over P :=
  ((Functor.const (Over P)).obj (⊤_ (Over P))).prod' (𝟭 (Over P))

/-- The global slice polynomial uses its chosen products and coproducts. -/
def polynomial : Over P ⥤ Over P :=
  insert P ⋙ (ForkFormulaParameterChange.template.mapCoefficients
    (SlicePolynomialComparison.globalCoefficients (coefficients D) P)).eval

/-- The target functor is the exact canonical parameterized expression. -/
theorem polynomial_eq : polynomial D P = insert P ⋙
    ((ForkFormulaParameterChange.template.mapCoefficients (coefficients D)).withParameters P).eval := by
  rw [SlicePolynomialComparison.withParameters_eq (coefficients D) P
    ForkFormulaParameterChange.template]
  rfl

abbrev carriers (B : Endofunctor.Algebra (polynomial D P)) : Over P × Over P :=
  (⊤_ (Over P), B.a)

/-- The five component operations are obtained from the global target.
Their transition square is proved by `operation_square`. -/
def target (B : Endofunctor.Algebra (polynomial D P)) :
    ForkParameterizedFormulaFolds.Algebra D P where
  carrier := B.a
  str j := SlicePolynomialComparison.operation (coefficients D) P
    ForkFormulaParameterChange.template (carriers D P B) B.a B.str j
  naturality {_ _} f :=
    SlicePolynomialComparison.operation_square (coefficients D) P
      ForkFormulaParameterChange.template (carriers D P B) B.a B.str f

/-- The proved natural component folds now apply to every canonical
slice target, including nonconstant carrier families. -/
def fold (B : Endofunctor.Algebra (polynomial D P)) :
    ForkParameterizedFormulaFolds.parameterCarrier D P ⟶ B.a :=
  (ForkParameterizedFormulaFolds.fold D P (target D P B)).f

theorem fold_over (B : Endofunctor.Algebra (polynomial D P)) :
    (fold D P B).left ≫ B.a.hom =
      (ForkParameterizedFormulaFolds.parameterCarrier D P).hom := Over.w _

theorem fold_constructor (B : Endofunctor.Algebra (polynomial D P)) (j : WalkingSpan) :
    (ForkParameterizedFormulaFolds.polynomial D P j).map
        (ForkParameterizedFormulaFolds.componentHom P (fold D P B) j) ≫
      (target D P B).str j =
    (ForkParameterizedFormulaFolds.algebra D P).str j ≫
      ForkParameterizedFormulaFolds.componentHom P (fold D P B) j :=
  ForkParameterizedFormulaFolds.fold_constructor D P (target D P B) j

/-- Every underlying natural morphism over P satisfying the component constructor
equations is the constructed fold. -/
theorem fold_underlying_unique (B : Endofunctor.Algebra (polynomial D P))
    (m : ForkParameterizedFormulaFolds.parameterCarrier D P ⟶ B.a)
    (hm : ∀ j, (ForkParameterizedFormulaFolds.polynomial D P j).map
        (ForkParameterizedFormulaFolds.componentHom P m j) ≫ (target D P B).str j =
      (ForkParameterizedFormulaFolds.algebra D P).str j ≫
        ForkParameterizedFormulaFolds.componentHom P m j) : m = fold D P B :=
  ForkParameterizedFormulaFolds.fold_underlying_unique D P (target D P B) m hm

/-- A natural fold also exists from the canonical constant-family carrier. -/
def constantFold (B : Endofunctor.Algebra (polynomial D P)) :
    constantFamily P (ForkFirstOrderFormula.algebra D).a ⟶ B.a :=
  (ForkParameterizedFormulaFolds.parameterCarrierIso D P).inv ≫ fold D P B

theorem constantFold_over (B : Endofunctor.Algebra (polynomial D P)) :
    (constantFold D P B).left ≫ B.a.hom =
      (constantFamily P (ForkFirstOrderFormula.algebra D).a).hom := Over.w _

end CategoricalEssentialIncompleteness.V46.ForkCanonicalParameterTargets
