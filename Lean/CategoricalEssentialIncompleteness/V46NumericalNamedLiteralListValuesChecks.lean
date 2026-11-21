/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalNamedLiteralListValues


/-! # Numerical list constructors have the finite-word values -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.NumericalNamedLiteralListValuesChecks
open NumericalNamed
variable (V : NumericalTuples.Object) (σ π : ℕ → NumericalTuples.Object) (d : ℕ)

example (word : ℕ) :
    (literalSourceSyntax V σ π d).lists.algebra.carrier.val.Evalb (M := ℕ) ![word] ↔
      ∀ i < len word, nth word i ∈ NumericalTuples.codedSupport V :=
  literal_listCarrier_eval V σ π d word

example : (literalCategoricalSyntax V σ π d).lists.algebra.nil ≫
      (literalListPresentationIso V σ π d).hom =
    (literalListNilInputPresentationIso).hom ≫
      NumericalCoordinates.predicateMap (literalSourceSyntax V σ π d).lists.algebra.nil :=
  literal_listNil_code_square V σ π d

example : (literalCategoricalSyntax V σ π d).lists.algebra.cons ≫
      (literalListPresentationIso V σ π d).hom =
    (literalListConsInputPresentationIso V σ π d).hom ≫
      NumericalCoordinates.predicateMap (literalSourceSyntax V σ π d).lists.algebra.cons :=
  literal_listCons_code_square V σ π d

example (x : NumericalTuples.Point (⊤_ NumericalTuples.Object)) :
    ((literalListPresentationIso V σ π d).hom.toFun
      ((literalCategoricalSyntax V σ π d).lists.algebra.nil.toFun x)).val = (0 : ℕ) :=
  literal_listNil_value V σ π d x

end CategoricalEssentialIncompleteness.V46.NumericalNamedLiteralListValuesChecks
