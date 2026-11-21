/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkDerivationGluing


/-! # Compatible constructors and folds on the original proof fork -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkDerivation.Checks

example (a b : Idem EffectiveFork.V) {j k : WalkingSpan} (g : j ⟶ k) :
    (componentTransition g).app ((rules a b).inference.obj (proofSlice a b)).left ≫
        constructorComponent a b k =
      constructorComponent a b j ≫ (componentTransition g).app (proofObject a b) :=
  constructorComponents_natural a b g

example (a b : Idem EffectiveFork.V) (B : Endofunctor.Algebra (rules a b).inference)
    {j k : WalkingSpan} (g : j ⟶ k) :
    (componentTransition g).app (proofObject a b) ≫ foldedComponent a b B k =
      foldedComponent a b B j ≫ (componentTransition g).app B.a.left :=
  foldComponents_natural a b B g

example (a b : Idem EffectiveFork.V) {j k : WalkingSpan} (g : j ⟶ k) :
    Naturality.AlgebraNaturality
      (componentSupport_re j a) (componentSupport_re j b)
      (componentSupport_re k a) (componentSupport_re k b)
      (pointwiseAlgebra a b j) (pointwiseAlgebra a b k)
      (spanAtoms g) (spanAtoms_computable g) (componentSupport_map g a) (componentSupport_map g b)
      ((componentTransition g).app (proofObject a b)) (componentOver_transition (proofSlice a b) g) :=
  pointwiseAlgebra_naturality a b g

end CategoricalEssentialIncompleteness.V46.ForkDerivation.Checks
