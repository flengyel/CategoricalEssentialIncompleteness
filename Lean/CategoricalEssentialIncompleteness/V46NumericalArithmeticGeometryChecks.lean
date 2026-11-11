/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalArithmeticGeometry


/-! # Statement checks in `V46NumericalArithmeticGeometryChecks` -/

@[expose] public section
noncomputable section
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
namespace CategoricalEssentialIncompleteness.V46.NumericalArithmetic.Geometry.Checks
example : PreservesFiniteLimits numericalInterpretation := inferInstance
example : PreservesColimitsOfShape (Discrete WalkingPair) numericalInterpretation := inferInstance
example (C D : PredicateCategory 𝗣𝗔) :
    (productIso C D).hom ≫ prod.fst = numericalInterpretation.map (prod.fst : C ⨯ D ⟶ C) :=
  product_fst C D
example (C D : PredicateCategory 𝗣𝗔) :
    numericalInterpretation.map (coprod.inl : C ⟶ C ⨿ D) ≫ (coproductIso C D).hom = coprod.inl :=
  coproduct_inl C D
example {A B C : PredicateCategory 𝗣𝗔} (f : A ⟶ C) (g : B ⟶ C) :
    (pullbackIso f g).hom ≫ pullback.snd _ _ = numericalInterpretation.map (pullback.snd f g) :=
  pullback_snd f g
end CategoricalEssentialIncompleteness.V46.NumericalArithmetic.Geometry.Checks
