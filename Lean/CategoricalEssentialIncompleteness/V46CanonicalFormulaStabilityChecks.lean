/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46ForkCanonicalFormulaStability

/-! # Independent checks of canonical formula parameter initiality

This checks the complete five-branch formula algebra in every global
parameter slice. The full term/formula interface, lists, substitution
and derivations remain separate obligations in Proposition 10.7.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46
namespace CategoricalEssentialIncompleteness.V46.CanonicalFormulaStabilityStatementChecks
open ForkFirstOrderFormula
variable (D P : Object)

/-- The source constructor is exactly the formula projection of the
canonical parameterization of the constructed global constructor. -/
example : (ForkCanonicalFormulaSource.algebra D P).str =
    (SyntaxPolynomial.algebraWithParameters .unit
      (ForkFormulaParameterChange.template.mapCoefficients
        (ForkCanonicalParameterTargets.coefficients D))
      (ForkCanonicalFormulaSource.jointAlgebra D) P).str.2 := rfl

/-- The relative polynomial has all five printed summands in their
specified order, using the chosen products in the global slice. -/
example (Y : Over P) : (ForkCanonicalParameterTargets.polynomial D P).obj Y =
    (((((constantFamily P numbers ⨯ constantFamily P numbers) ⨿ constantFamily P D) ⨿ Y) ⨿
      (Y ⨯ Y)) ⨿ (constantFamily P numbers ⨯ Y)) := rfl

example : (ForkCanonicalFormulaSource.algebra D P).a =
    constantFamily P (ForkFirstOrderFormula.algebra D).a := rfl

/-- Every parameter diagram and coefficient diagram is included. The
statement has no supplied constructor-compatibility or initiality premise. -/
example : IsInitial (ForkCanonicalFormulaSource.algebra D P) :=
  ForkCanonicalFormulaStability.initial D P

/-- The target is any algebra in the actual global slice category;
its carrier may be nonconstant over P. -/
example (B : Endofunctor.Algebra (ForkCanonicalParameterTargets.polynomial D P)) :
    (ForkCanonicalParameterTargets.polynomial D P).map
        (ForkCanonicalFormulaStability.fold D P B).f ≫ B.str =
      (ForkCanonicalFormulaSource.algebra D P).str ≫
        (ForkCanonicalFormulaStability.fold D P B).f :=
  (ForkCanonicalFormulaStability.fold D P B).h

/-- The uniqueness quantifier ranges over every underlying natural
morphism over P satisfying the single full global constructor equation. -/
example (B : Endofunctor.Algebra (ForkCanonicalParameterTargets.polynomial D P))
    (m : (ForkCanonicalFormulaSource.algebra D P).a ⟶ B.a)
    (hm : (ForkCanonicalParameterTargets.polynomial D P).map m ≫ B.str =
      (ForkCanonicalFormulaSource.algebra D P).str ≫ m) :
    m = (ForkCanonicalFormulaStability.fold D P B).f :=
  ForkCanonicalFormulaStability.fold_underlying_unique D P B m hm

example (B : Endofunctor.Algebra (ForkCanonicalParameterTargets.polynomial D P)) :
    (ForkCanonicalFormulaStability.fold D P B).f.left ≫ B.a.hom =
      (constantFamily P (ForkFirstOrderFormula.algebra D).a).hom := Over.w _

#print axioms PolynomialInputComposition.input_id
#print axioms PolynomialInputComposition.component_comp
#print axioms PolynomialInputComposition.input_comp
#print axioms PolynomialParameterValues.value_as_input
#print axioms SliceParameterConstructorComparison.coefficient_value
#print axioms SliceParameterConstructorComparison.coefficient_natural
#print axioms SliceParameterConstructorComparison.relativeInput
#print axioms SliceParameterConstructorComparison.value_square
#print axioms SliceParameterConstructorComparison.comparison_square
#print axioms ForkCanonicalFormulaSource.comparison
#print axioms ForkCanonicalFormulaSource.constructor
#print axioms ForkCanonicalFormulaSource.jointAlgebra
#print axioms ForkCanonicalFormulaSource.algebra
#print axioms ForkCanonicalFormulaSource.parameter_structure
#print axioms ForkCanonicalFormulaSource.source_square
#print axioms ForkCanonicalFormulaSource.source_hom
#print axioms AlgebraEvaluation.algebra
#print axioms AlgebraEvaluation.hom_condition_iff
#print axioms ForkCanonicalFormulaStability.componentIso
#print axioms ForkCanonicalFormulaStability.sourceIso
#print axioms ForkCanonicalFormulaStability.componentInitial
#print axioms ForkCanonicalFormulaStability.fold_component
#print axioms ForkCanonicalFormulaStability.fold_local_constructor
#print axioms ForkCanonicalFormulaStability.fold_constructor
#print axioms ForkCanonicalFormulaStability.fold
#print axioms ForkCanonicalFormulaStability.initial
#print axioms ForkCanonicalFormulaStability.fold_underlying_unique
end CategoricalEssentialIncompleteness.V46.CanonicalFormulaStabilityStatementChecks
