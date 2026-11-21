/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ForkDerivationAlgebra


/-! # The inference constructor on the original fork proof carrier -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkDerivation
variable (a b : Idem EffectiveFork.V)

example : (proofSlice a b).left = (⟨ForkSyntax.Prf a b⟩ : EffectiveFork.Total) := rfl
example : (proofSlice a b).hom =
    (⟨ForkSyntax.conclusion a b,ForkSyntax.conclusion_total a b⟩ :
      (⟨ForkSyntax.Prf a b⟩ : EffectiveFork.Total) ⟶ (⟨ForkSyntax.S⟩ : EffectiveFork.Total)) := rfl
example (j : WalkingSpan) : IsInitial (pointwiseAlgebra a b j) := pointwiseInitial a b j
example (j : WalkingSpan) :
    constructorComponent a b j ≫ (componentProofIso a b j).hom =
      (componentInputIso a b (proofSlice a b) j).hom ≫
        ((nativeRules a b j).inference.map (componentProofSliceIso a b j).hom).left ≫
          (nativeAlgebra a b j).str.left := constructorComponent_native a b j
example (j : WalkingSpan) :
    constructorComponent a b j ≫ (componentFunctor j).map (conclusion a b) =
      (componentFunctor j).map ((rules a b).inference.obj (proofSlice a b)).hom :=
  constructorComponent_conclusion a b j
example (B : Endofunctor.Algebra (rules a b).inference) (j : WalkingSpan) :
    foldedComponent a b B j ≫ (componentFunctor j).map B.a.hom =
      (componentFunctor j).map (conclusion a b) := foldedComponent_conclusion a b B j
example (B : Endofunctor.Algebra (rules a b).inference) (j : WalkingSpan) :
    foldedComponentHom a b B j = (pointwiseAlgebraIso a b j).hom ≫
      Naturality.foldHom (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b) (componentAlgebra a b B j) :=
  foldedComponentHom_eq_native a b B j
end CategoricalEssentialIncompleteness.V46.ForkDerivation
