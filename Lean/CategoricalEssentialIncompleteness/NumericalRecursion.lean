/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.NumericalIsotype
public import CategoricalEssentialIncompleteness.NumericalTuring

/-!
# The numerical recursion category

The numerical category is a prodominical isotype with a Turing morphism. Choosing a
code for each partial recursive morphism defines an ordinary function on extensional
hom-sets that supplies its total parameter map. The evaluation equation recovers the
given partial morphism from that map.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory
open Nat.Partrec (Code)
namespace CategoricalEssentialIncompleteness
namespace Numerical

/-- The concrete numerical category, equipped with universal program evaluation,
is a `P`-recursion category. -/
instance numericalRecursionCategory : RecursionCategory.PRecursionCategory Numerical where
  W := nat
  X := nat
  Y := nat
  tau := turingEvaluator
  is_turing := turingEvaluator_isTuringMorphism

/-- Choose a program code for each extensional partial morphism and form its total
parameter map. -/
def turingIndexing (V : Numerical) (φ : product V nat ⟶ nat) :
    totalObject V ⟶ totalObject nat :=
  codeParameter V
    (Classical.choose (Code.exists_code.mp (Partrec.nat_iff.mp φ.computable)))

/-- Evaluation of the chosen total parameter map recovers the original partial recursive
morphism, including its domain of definition. -/
theorem turingIndexing_evaluation (V : Numerical) (φ : product V nat ⟶ nat) :
    partialProdMap (turingIndexing V φ).hom (𝟙 nat) ≫ turingEvaluator = φ :=
  turingEvaluator_parameterization V φ _
    (Classical.choose_spec (Code.exists_code.mp (Partrec.nat_iff.mp φ.computable)))

end Numerical
end CategoricalEssentialIncompleteness
