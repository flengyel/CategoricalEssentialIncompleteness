/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46PolynomialParameterSquares
public import CategoricalEssentialIncompleteness.V46ForkFormulaParameterChange

/-! # Constructor squares before numerical algebra specialization -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ForkFormulaSquareTransport
open ForkFirstOrderFormula PolynomialParameterSquares
local instance (P : C) : Regular (Over P) := RegularSlices.regular P

abbrev labels (N D : C) (t : Bool) : C := if t then D else N

def labelMap (N : C) {D E : C} (h : D ⟶ E) (t : Bool) : labels N D t ⟶ labels N E t :=
  match t with
  | false => 𝟙 N
  | true => h

abbrev PairAlgebra (N D : C) :=
  Endofunctor.Algebra (SyntaxPolynomial.jointFunctor .unit (expression N D))

def formulaOfPair (N D : C) (A : PairAlgebra N D) :
    Endofunctor.Algebra (ForkFirstOrderFormula.polynomial N D) := ⟨A.a.2, A.str.2⟩

def parameterOfPair (N D P : C) (A : PairAlgebra N D) :
    Endofunctor.Algebra (ForkFormulaParameterComponents.polynomial N D P) :=
  ⟨constantFamily P A.a.2,
    (SyntaxPolynomial.algebraWithParameters .unit (expression N D) A P).str.2⟩

theorem parameter_structure (N D P : C) (A : PairAlgebra N D) :
    (parameterOfPair N D P A).str =
      PolynomialParameterValues.comparison P (labels N D) (⊤_ C, A.a.2)
          ForkFormulaParameterChange.template ≫
        (constantFamilyFunctor P).map A.str.2 := rfl

/-- The two ignored term carriers remain abstract in this comparison. -/
theorem relative_input (N D E P Q X Y : C) (b : P ⟶ Q) (h : D ⟶ E) (k : X ⟶ Y) :
    relativeInput b (labelMap N h) (⊤_ C, X) (⊤_ C, Y) (𝟙 _, k)
        ForkFormulaParameterChange.template =
      (ForkFormulaParameterChange.comparison N b h).app (constantFamily P X) ≫
        (ForkFormulaParameterComponents.polynomial N E Q).map (familyMap b k) := by
  have hc : (fun t => familyMap b (labelMap N h t)) =
      ForkFormulaParameterChange.coefficientMap N b h := by
    funext t
    cases t <;> rfl
  dsimp only [relativeInput, LaxPolynomialComparison.input]
  rw [hc]
  rfl

/-- This statement is proved for arbitrary algebra records; numerical
initiality is used only in the later application. -/
theorem constructor_square (N D E P Q : C) (b : P ⟶ Q) (h : D ⟶ E)
    (A : PairAlgebra N D) (B : PairAlgebra N E) (k : A.a.2 ⟶ B.a.2)
    (hk : baseInput (labelMap N h) (⊤_ C, A.a.2) (⊤_ C, B.a.2) (𝟙 _, k)
        ForkFormulaParameterChange.template ≫ B.str.2 = A.str.2 ≫ k) :
    (ForkFormulaParameterChange.comparison N b h).app (constantFamily P A.a.2) ≫
      (ForkFormulaParameterComponents.polynomial N E Q).map (familyMap b k) ≫
        (parameterOfPair N E Q B).str =
      (Over.map b).map (parameterOfPair N D P A).str ≫ familyMap b k := by
  rw [← Category.assoc, ← relative_input N D E P Q A.a.2 B.a.2 b h k,
    parameter_structure, parameter_structure]
  rw [← Category.assoc,
    comparison_square b (labelMap N h) (⊤_ C, A.a.2) (⊤_ C, B.a.2) (𝟙 _, k)
      ForkFormulaParameterChange.template,
    Category.assoc]
  have ht {U V W : C} (f : U ⟶ V) (g : V ⟶ W) :
      familyMap b f ≫ (constantFamilyFunctor Q).map g = familyMap b (f ≫ g) := by
    apply Over.OverMorphism.ext
    change prod.map b f ≫ prod.map (𝟙 Q) g = _
    rw [prod.map_map, Category.comp_id]
    rfl
  have hs {U V W : C} (f : U ⟶ V) (g : V ⟶ W) :
      (Over.map b).map ((constantFamilyFunctor P).map f) ≫ familyMap b g =
        familyMap b (f ≫ g) := by
    apply Over.OverMorphism.ext
    change prod.map (𝟙 P) f ≫ prod.map b g = _
    rw [prod.map_map, Category.id_comp]
    rfl
  rw [Functor.map_comp, Category.assoc, ht, hs, hk]
end CategoricalEssentialIncompleteness.V46.ForkFormulaSquareTransport
