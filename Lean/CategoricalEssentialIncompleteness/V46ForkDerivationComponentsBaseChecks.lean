/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkDerivationComponentsBase


/-! # Statement checks in `V46ForkDerivationComponentsBaseChecks` -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkDerivation.Checks

example (j : WalkingSpan) :
    (componentFunctor j).map implication ≫ (componentFormulaIso j).hom =
      (componentPowerIso j 2).hom ≫ Component.implication := component_implication j

example (a b : Idem EffectiveFork.V) (j : WalkingSpan) (i : Fin 3) :
    (componentRuleIso a b j i).hom ≫
      (Component.rules (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b)).premises i =
      (componentRebasedRules a b j).premises i := component_rule_premises a b j i

example (a b : Idem EffectiveFork.V) (j : WalkingSpan) (i : Fin 3) :
    (componentRuleIso a b j i).hom ≫
      (Component.rules (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b)).conclusion i =
      (componentRebasedRules a b j).conclusion i := component_rule_conclusion a b j i

example (a b : Idem EffectiveFork.V) (Q : Over sentenceObject) (j : WalkingSpan) :
    (componentFunctor j).obj ((rules a b).inference.obj Q).left ≅
      ((Component.rules (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b)).inference.obj (componentOver Q j)).left :=
  componentInputIso a b Q j

example (a b : Idem EffectiveFork.V) (Q : Over sentenceObject) (j : WalkingSpan) :
    (componentInputIso a b Q j).hom ≫
      ((Component.rules (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b)).inference.obj (componentOver Q j)).hom =
      (componentFunctor j).map ((rules a b).inference.obj Q).hom ≫ (componentFormulaIso j).hom :=
  componentInputIso_conclusion a b Q j

example (a b : Idem EffectiveFork.V) {Q Q' : Over sentenceObject} (f : Q ⟶ Q') (j : WalkingSpan) :
    (componentFunctor j).map ((rules a b).inference.map f).left ≫ (componentInputIso a b Q' j).hom =
      (componentInputIso a b Q j).hom ≫
        ((Component.rules (componentSupport j a) (componentSupport j b)
          (componentSupport_re j a) (componentSupport_re j b)).inference.map (componentOverMap f j)).left :=
  componentInputIso_natural a b f j

example (a b : Idem EffectiveFork.V) (B : Endofunctor.Algebra (rules a b).inference) (j : WalkingSpan) :
    (componentAlgebra a b B j).a.left = (componentFunctor j).obj B.a.left := rfl

example (a b : Idem EffectiveFork.V) (B : Endofunctor.Algebra (rules a b).inference) (j : WalkingSpan) :
    (componentAlgebra a b B j).str.left =
      (componentInputIso a b B.a j).inv ≫ (componentFunctor j).map B.str.left :=
  componentAlgebra_str_left a b B j

example (a b : Idem EffectiveFork.V)
    (A B : Endofunctor.Algebra (rules a b).inference) (f : A.a ⟶ B.a) (j : WalkingSpan) :
    (Component.rules (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b)).inference.map (componentOverMap f j) ≫
        (componentAlgebra a b B j).str =
      (componentAlgebra a b A j).str ≫ componentOverMap f j ↔
    (componentFunctor j).map (((rules a b).inference.map f) ≫ B.str).left =
      (componentFunctor j).map (A.str ≫ f).left := component_hom_condition a b A B f j

example (a b : Idem EffectiveFork.V) {A B : Endofunctor.Algebra (rules a b).inference}
    (f : A ⟶ B) (j : WalkingSpan) :
    ((toComponentAlgebra a b j).map f).f.left = (componentFunctor j).map f.f.left := rfl

end CategoricalEssentialIncompleteness.V46.ForkDerivation.Checks
