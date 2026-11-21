/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46ForkFormulaSquareTransport

/-! # Concrete constructor squares for parameterized fork formula transitions -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ForkFormulaTransitionSquares
open ForkFirstOrderFormula PolynomialParameterSquares ForkFormulaSquareTransport
local instance (P : C) : Regular (Over P) := RegularSlices.regular P

abbrev parameterMap (N D E P Q : C) (b : P ⟶ Q)
    (k : (componentAlgebra N D).a ⟶ (componentAlgebra N E).a) :
    (Over.map b).obj (constantFamily P (componentAlgebra N D).a) ⟶
      constantFamily Q (componentAlgebra N E).a := familyMap b k

/-- The generic constructor square is applied to the existing numerical
algebras, with all carrier and coefficient parameters specified. -/
theorem source_square (N D E P Q : C) (b : P ⟶ Q) (h : D ⟶ E)
    (k : (componentAlgebra N D).a ⟶ (componentAlgebra N E).a)
    (hk : baseInput (labelMap N h) (⊤_ C, (componentAlgebra N D).a)
        (⊤_ C, (componentAlgebra N E).a) (𝟙 _, k) ForkFormulaParameterChange.template ≫
      (componentAlgebra N E).str = (componentAlgebra N D).str ≫ k) :
    (ForkFormulaParameterChange.comparison N b h).app
        (constantFamily P (componentAlgebra N D).a) ≫
      (ForkFormulaParameterComponents.polynomial N E Q).map (parameterMap N D E P Q b k) ≫
        (ForkFormulaParameterComponents.algebra N E Q).str =
      (Over.map b).map (ForkFormulaParameterComponents.algebra N D P).str ≫
        parameterMap N D E P Q b k :=
  constructor_square N D E P Q b h (pairAlgebra N D) (pairAlgebra N E) k hk

theorem base_input (N D E X Y : C) (h : D ⟶ E) (k : X ⟶ Y) :
    baseInput (labelMap N h) (⊤_ C, X) (⊤_ C, Y) (𝟙 _, k)
        ForkFormulaParameterChange.template =
      (ForkFirstOrderFormula.transition h N).app X ≫
        (ForkFirstOrderFormula.polynomial N E).map k := by
  dsimp [baseInput, SyntaxCoefficientMorphisms.component,
    ForkFormulaParameterChange.template, labelMap, labels,
    ForkFirstOrderFormula.transition, ForkFirstOrderFormula.polynomial,
    ForkFirstOrderFormula.insert, ForkFirstOrderFormula.expression,
    SyntaxPolynomial.mapCoefficients, SyntaxPolynomial.eval, SyntaxPolynomial.sumFunctor,
    SyntaxPolynomial.productFunctor, Functor.comp_obj, Functor.comp_map,
    Functor.prod'_obj, Functor.prod'_map, Functor.const_obj_obj, Functor.const_obj_map,
    Functor.id_obj, Functor.id_map]
  simp only [prod.map_id_id]

/-- The fork transitions satisfy the constructor square. -/
theorem fork_source_square (D P : Object) {j l : WalkingSpan} (f : j ⟶ l) :
    (ForkFormulaParameterChange.comparison (numbers.obj j) (P.map f) (D.map f)).app
        (constantFamily (P.obj j) (componentAlgebra (numbers.obj j) (D.obj j)).a) ≫
      (ForkFormulaParameterComponents.polynomial (numbers.obj l) (D.obj l) (P.obj l)).map
        (parameterMap (numbers.obj j) (D.obj j) (D.obj l) (P.obj j) (P.obj l) (P.map f)
          ((ForkFirstOrderFormula.algebra D).a.map f)) ≫
      (ForkFormulaParameterComponents.algebra (numbers.obj l) (D.obj l) (P.obj l)).str =
    (Over.map (P.map f)).map
        (ForkFormulaParameterComponents.algebra (numbers.obj j) (D.obj j) (P.obj j)).str ≫
      parameterMap (numbers.obj j) (D.obj j) (D.obj l) (P.obj j) (P.obj l) (P.map f)
        ((ForkFirstOrderFormula.algebra D).a.map f) := by
  apply source_square (numbers.obj j) (D.obj j) (D.obj l) (P.obj j) (P.obj l)
    (P.map f) (D.map f) ((ForkFirstOrderFormula.algebra D).a.map f)
  rw [base_input (numbers.obj j) (D.obj j) (D.obj l)
    (componentAlgebra (numbers.obj j) (D.obj j)).a
    (componentAlgebra (numbers.obj j) (D.obj l)).a
    (D.map f) ((ForkFirstOrderFormula.algebra D).a.map f)]
  have hn := (ForkFirstOrderFormula.transition (D.map f) (numbers.obj j)).naturality
    ((ForkFirstOrderFormula.algebra D).a.map f)
  have hc := DiagramInitialAlgebras.transition_constructor
    (ForkFirstOrderFormula.polynomialDiagram D)
    (fun j => componentAlgebra (numbers.obj j) (D.obj j))
    (fun j => componentInitial (numbers.obj j) (D.obj j)) f
  calc
    _ = ((ForkFirstOrderFormula.polynomial (numbers.obj j) (D.obj j)).map
        ((ForkFirstOrderFormula.algebra D).a.map f) ≫
      (ForkFirstOrderFormula.transition (D.map f) (numbers.obj j)).app
        (componentAlgebra (numbers.obj j) (D.obj l)).a) ≫
          (componentAlgebra (numbers.obj j) (D.obj l)).str :=
      congrArg (fun m => m ≫ (componentAlgebra (numbers.obj j) (D.obj l)).str) hn.symm
    _ = _ := by
      simpa only [Category.assoc, ForkFirstOrderFormula.polynomialDiagram,
        ForkFirstOrderFormula.algebra, DiagramInitialAlgebras.algebra,
        DiagramInitialAlgebras.carrier, numbers, Functor.const_obj_obj] using hc
end CategoricalEssentialIncompleteness.V46.ForkFormulaTransitionSquares
