/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkDerivationComponentsCoordinates


/-! # The component objects and finite coefficient charts -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkDerivation.CoordinatesChecks

example (j : WalkingSpan) : PreservesFiniteLimits (componentFunctor j) := inferInstance
example (j : WalkingSpan) : PreservesFiniteCoproducts (componentFunctor j) := inferInstance
example (a b : Idem EffectiveFork.V) (j : WalkingSpan) :
    (componentFunctor j).map (conclusion a b) ≫ (componentFormulaIso j).hom =
      (componentProofIso a b j).hom ≫ Component.conclusion (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b) := component_conclusion a b j
example (a : Idem EffectiveFork.V) (j : WalkingSpan) :
    (componentFunctor j).map (axiomInclusion a) ≫ (componentVariableIso j).hom =
      (componentAxiomDomainIso j a).hom ≫ nativeInclusion (componentSupport j a) (componentSupport_re j a) :=
  component_axiomInclusion j a
example (j : WalkingSpan) :
    (componentFunctor j).map implication ≫ (componentFormulaIso j).hom =
      (componentPowerIso j 2).hom ≫ Component.implication := component_implication j
example {X : EffectiveFork.Total} (j : WalkingSpan) (f g : X ⟶ sentenceObject) :
    (componentFunctor j).map (prod.lift f g) ≫ (componentPowerIso j 2).hom =
      prod.lift ((componentFunctor j).map f ≫ (componentFormulaIso j).hom)
        ((componentFunctor j).map g ≫ (componentFormulaIso j).hom) := component_pair j f g
example (a b : Idem EffectiveFork.V) (j : WalkingSpan)
    (x : NumericalTuples.Point ((componentFunctor j).obj (proofObject a b))) :
    ((componentProofIso a b j).hom.toFun x).val = x.val := componentProofIso_value a b j x
example {X Y : EffectiveFork.Total} (f : ∀ j, (componentFunctor j).obj X ⟶ (componentFunctor j).obj Y)
    (hn : ∀ ⦃j k : WalkingSpan⦄ (g : j ⟶ k),
      Naturality.unaryFunctor.map ((EffectiveFork.totalFunctor.obj X).map g) ≫ f k =
        f j ≫ Naturality.unaryFunctor.map ((EffectiveFork.totalFunctor.obj Y).map g)) (j : WalkingSpan) :
    (componentFunctor j).map (fromComponents f hn) = f j := component_fromComponents f hn j

end CategoricalEssentialIncompleteness.V46.ForkDerivation.CoordinatesChecks
