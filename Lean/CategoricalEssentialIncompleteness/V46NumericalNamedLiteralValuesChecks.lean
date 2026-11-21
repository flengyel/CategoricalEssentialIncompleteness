/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralValues


/-! # Numerical free-variable diagrams and primitive traversal values -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.NumericalNamedLiteralValuesChecks
open NumericalNamed
variable (V : NumericalTuples.Object) (σ π : ℕ → NumericalTuples.Object) (d : ℕ)

example : (literalCategoricalSyntax V σ π d).formulaOccurrences ≫ (literalListPresentationIso V σ π d).hom =
    (literalFormulaPresentationIso V σ π d).hom ≫
      NumericalCoordinates.predicateMap (literalSourceSyntax V σ π d).formulaOccurrences :=
  literal_formulaOccurrences_code_square V σ π d
example (x : NumericalTuples.Point (literalCategoricalSyntax V σ π d).algebra.a.2) :
    ((literalListPresentationIso V σ π d).hom.toFun
      ((literalCategoricalSyntax V σ π d).formulaOccurrences.toFun x)).val =
    ConcreteNamedSubstitution.freeVariables (M := ℕ) (NumericalCoordinates.codedPredicate V)
      (fun n => NumericalCoordinates.codedPredicate (σ n))
      (fun n => NumericalCoordinates.codedPredicate (π n)) d
      ((literalFormulaPresentationIso V σ π d).hom.toFun x).val :=
  literal_formulaOccurrences_value V σ π d x

end CategoricalEssentialIncompleteness.V46.NumericalNamedLiteralValuesChecks
