/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46SliceParameterConstructorComparison
public import CategoricalEssentialIncompleteness.V46ForkCanonicalParameterTargets
public import CategoricalEssentialIncompleteness.V46NumericalCanonicalDiagramSyntax

/-! # The canonical global formula source and its parameter constructor -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.ForkCanonicalFormulaSource
open ForkFirstOrderFormula
variable (D : Object)
abbrev coefficients := ForkCanonicalParameterTargets.coefficients D
abbrev template := ForkFormulaParameterChange.template
abbrev carrier := (ForkFirstOrderFormula.algebra D).a
abbrev baseCarriers : Object × Object := (⊤_ Object, carrier D)

def comparison : (template.mapCoefficients (coefficients D)).eval.obj (baseCarriers D) ⟶
    (DiagramInitialAlgebras.diagonal (polynomialDiagram D)).obj (carrier D) where
  app j := DiagramPolynomialComparison.component (coefficients D) (baseCarriers D) template j
  naturality {j k} f := by
    have h := DiagramPolynomialComparison.component_transition (coefficients D)
      (baseCarriers D) template f
    have ht : DiagramPolynomialComparison.transition (coefficients D) (baseCarriers D) template f =
        ((DiagramInitialAlgebras.diagonal (polynomialDiagram D)).obj (carrier D)).map f := by
      rw [ForkFirstOrderFormula.polynomial_transition]
      change coprod.map (coprod.map (coprod.map (coprod.map (prod.map (𝟙 _) (𝟙 _))
        (D.map f)) ((carrier D).map f)) (prod.map ((carrier D).map f) ((carrier D).map f)))
          (prod.map (𝟙 _) ((carrier D).map f)) = _
      rw [prod.map_id_id]
      rfl
    exact h.trans (congrArg (fun m => DiagramPolynomialComparison.component (coefficients D)
      (baseCarriers D) template j ≫ m) ht)

def constructor : (template.mapCoefficients (coefficients D)).eval.obj (baseCarriers D) ⟶
    carrier D := comparison D ≫ (ForkFirstOrderFormula.algebra D).str

def jointAlgebra : Endofunctor.Algebra (SyntaxPolynomial.jointFunctor .unit
    (template.mapCoefficients (coefficients D))) :=
  ⟨baseCarriers D, (terminal.from _, constructor D)⟩

variable (P : Object)

/-- The source is the formula projection of the exact canonical
`algebraWithParameters`, on the canonical constant-family carrier. -/
def algebra : Endofunctor.Algebra (ForkCanonicalParameterTargets.polynomial D P) :=
  ⟨constantFamily P (carrier D),
    (SyntaxPolynomial.algebraWithParameters .unit
      (template.mapCoefficients (coefficients D)) (jointAlgebra D) P).str.2⟩

theorem parameter_structure : (algebra D P).str =
    PolynomialParameterValues.comparison P (coefficients D) (baseCarriers D) template ≫
      (constantFamilyFunctor P).map (constructor D) := rfl

/-- Evaluation identifies the global parameter constructor with the already proved
numerical parameter constructor. -/
theorem source_square (j : WalkingSpan) :
    (SliceEvaluation.componentFunctor P j).map (algebra D P).str ≫
        (SliceEvaluation.coefficientIso P (carrier D) j).hom =
      SlicePolynomialComparison.component (coefficients D) P template
          (ForkCanonicalParameterTargets.carriers D P (algebra D P)) j ≫
        (ForkFormulaParameterComponents.polynomial (numbers.obj j) (D.obj j) (P.obj j)).map
          (SliceEvaluation.coefficientIso P (carrier D) j).hom ≫
        (ForkFormulaParameterComponents.algebra (numbers.obj j) (D.obj j) (P.obj j)).str := by
  rw [parameter_structure, Functor.map_comp, Category.assoc,
    SliceParameterConstructorComparison.coefficient_natural P (constructor D) j,
    ← Category.assoc]
  change _ ≫ (SliceEvaluation.coefficientIso P
      ((template.mapCoefficients (coefficients D)).eval.obj (baseCarriers D)) j).hom ≫
    (constantFamilyFunctor (P.obj j)).map
      (DiagramPolynomialComparison.component (coefficients D) (baseCarriers D) template j ≫
        (ForkFirstOrderFormula.algebra D).str.app j) = _
  rw [Functor.map_comp]
  have h := congrArg (fun m => m ≫ (constantFamilyFunctor (P.obj j)).map
      ((ForkFirstOrderFormula.algebra D).str.app j))
    (SliceParameterConstructorComparison.comparison_square (coefficients D) P
      (baseCarriers D) template j)
  have hι : SliceParameterConstructorComparison.relativeInput (coefficients D) P
      (baseCarriers D) template j =
      SlicePolynomialComparison.component (coefficients D) P template
          (ForkCanonicalParameterTargets.carriers D P (algebra D P)) j ≫
        (ForkFormulaParameterComponents.polynomial (numbers.obj j) (D.obj j) (P.obj j)).map
          (SliceEvaluation.coefficientIso P (carrier D) j).hom := rfl
  have hκ : (ForkFormulaParameterComponents.algebra (numbers.obj j) (D.obj j) (P.obj j)).str =
      PolynomialParameterValues.comparison (P.obj j) (fun i => (coefficients D i).obj j)
          ((baseCarriers D).1.obj j, (baseCarriers D).2.obj j) template ≫
        (constantFamilyFunctor (P.obj j)).map ((ForkFirstOrderFormula.algebra D).str.app j) := rfl
  rw [hι] at h
  rw [hκ]
  simpa only [Category.assoc] using h

/-- The carrier isomorphism is an algebra morphism at every component. -/
theorem source_hom (j : WalkingSpan) :
    (ForkFormulaParameterComponents.polynomial (numbers.obj j) (D.obj j) (P.obj j)).map
        (SliceEvaluation.coefficientIso P (carrier D) j).hom ≫
      (ForkFormulaParameterComponents.algebra (numbers.obj j) (D.obj j) (P.obj j)).str =
    (ForkCanonicalParameterTargets.target D P (algebra D P)).str j ≫
      (SliceEvaluation.coefficientIso P (carrier D) j).hom := by
  change _ = (inv (SlicePolynomialComparison.component (coefficients D) P template
      (ForkCanonicalParameterTargets.carriers D P (algebra D P)) j) ≫
    (SliceEvaluation.componentFunctor P j).map (algebra D P).str) ≫ _
  rw [Category.assoc, source_square, IsIso.inv_hom_id_assoc]

end CategoricalEssentialIncompleteness.V46.ForkCanonicalFormulaSource
