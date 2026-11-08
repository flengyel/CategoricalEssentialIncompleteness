/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ForkDerivationComponentsBase

/-! # The inference constructor on the original fork proof carrier -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.ForkDerivation

abbrev nativeRules (a b : Idem EffectiveFork.V) (j : WalkingSpan) :=
  Component.rules (componentSupport j a) (componentSupport j b)
    (componentSupport_re j a) (componentSupport_re j b)

abbrev nativeAlgebra (a b : Idem EffectiveFork.V) (j : WalkingSpan) :=
  Component.algebra (componentSupport j a) (componentSupport j b)
    (componentSupport_re j a) (componentSupport_re j b)

def proofSlice (a b : Idem EffectiveFork.V) : Over sentenceObject := Over.mk (conclusion a b)

def componentProofSliceIso (a b : Idem EffectiveFork.V) (j : WalkingSpan) :
    componentOver (proofSlice a b) j ≅ (nativeAlgebra a b j).a :=
  Over.isoMk (componentProofIso a b j) (component_conclusion a b j).symm

def pointwiseAlgebra (a b : Idem EffectiveFork.V) (j : WalkingSpan) :
    Endofunctor.Algebra (nativeRules a b j).inference where
  a := componentOver (proofSlice a b) j
  str := (nativeRules a b j).inference.map (componentProofSliceIso a b j).hom ≫
    (nativeAlgebra a b j).str ≫ (componentProofSliceIso a b j).inv

def pointwiseAlgebraIso (a b : Idem EffectiveFork.V) (j : WalkingSpan) :
    pointwiseAlgebra a b j ≅ nativeAlgebra a b j :=
  Endofunctor.Algebra.isoMk (componentProofSliceIso a b j) (by
    simp [pointwiseAlgebra,Category.assoc])

def pointwiseInitial (a b : Idem EffectiveFork.V) (j : WalkingSpan) :
    IsInitial (pointwiseAlgebra a b j) :=
  (Component.initial (componentSupport j a) (componentSupport j b)
    (componentSupport_re j a) (componentSupport_re j b)).ofIso (pointwiseAlgebraIso a b j).symm

/-- Each constructor evaluates only the selected, matched inference input. -/
def constructorComponent (a b : Idem EffectiveFork.V) (j : WalkingSpan) :
    (componentFunctor j).obj ((rules a b).inference.obj (proofSlice a b)).left ⟶
      (componentFunctor j).obj (proofObject a b) :=
  (componentInputIso a b (proofSlice a b) j).hom ≫ (pointwiseAlgebra a b j).str.left

/-- The constructor is the existing six-tag leaf/ordered-MP constructor
in the proved component coordinates. -/
theorem constructorComponent_native (a b : Idem EffectiveFork.V) (j : WalkingSpan) :
    constructorComponent a b j ≫ (componentProofIso a b j).hom =
      (componentInputIso a b (proofSlice a b) j).hom ≫
        ((nativeRules a b j).inference.map (componentProofSliceIso a b j).hom).left ≫
          (nativeAlgebra a b j).str.left := by
  have h := congrArg (fun m => m.left) (pointwiseAlgebraIso a b j).hom.h
  change ((componentInputIso a b (proofSlice a b) j).hom ≫ (pointwiseAlgebra a b j).str.left) ≫
      (componentProofIso a b j).hom = _
  erw [Category.assoc]
  exact congrArg (fun k => (componentInputIso a b (proofSlice a b) j).hom ≫ k) h.symm

theorem constructorComponent_over (a b : Idem EffectiveFork.V) (j : WalkingSpan) :
    constructorComponent a b j ≫ (componentOver (proofSlice a b) j).hom =
      (componentFunctor j).map ((rules a b).inference.obj (proofSlice a b)).hom ≫
        (componentFormulaIso j).hom := by
  erw [constructorComponent,Category.assoc,Over.w (pointwiseAlgebra a b j).str]
  exact componentInputIso_conclusion a b (proofSlice a b) j

theorem constructorComponent_conclusion (a b : Idem EffectiveFork.V) (j : WalkingSpan) :
    constructorComponent a b j ≫ (componentFunctor j).map (conclusion a b) =
      (componentFunctor j).map ((rules a b).inference.obj (proofSlice a b)).hom := by
  apply (cancel_mono (componentFormulaIso j).hom).1
  simpa only [Category.assoc,componentOver,proofSlice,Over.mk_hom] using
    constructorComponent_over a b j


def foldedComponentHom (a b : Idem EffectiveFork.V)
    (B : Endofunctor.Algebra (rules a b).inference) (j : WalkingSpan) :
    pointwiseAlgebra a b j ⟶ componentAlgebra a b B j :=
  (pointwiseInitial a b j).to (componentAlgebra a b B j)

def foldedComponent (a b : Idem EffectiveFork.V)
    (B : Endofunctor.Algebra (rules a b).inference) (j : WalkingSpan) :
    (componentFunctor j).obj (proofObject a b) ⟶ (componentFunctor j).obj B.a.left :=
  (foldedComponentHom a b B j).f.left

theorem foldedComponent_conclusion (a b : Idem EffectiveFork.V)
    (B : Endofunctor.Algebra (rules a b).inference) (j : WalkingSpan) :
    foldedComponent a b B j ≫ (componentFunctor j).map B.a.hom =
      (componentFunctor j).map (conclusion a b) := by
  apply (cancel_mono (componentFormulaIso j).hom).1
  have h := Over.w (foldedComponentHom a b B j).f
  change foldedComponent a b B j ≫
      ((componentFunctor j).map B.a.hom ≫ (componentFormulaIso j).hom) =
    (componentFunctor j).map (conclusion a b) ≫ (componentFormulaIso j).hom at h
  simpa only [Category.assoc] using h

theorem foldedComponentHom_eq_native (a b : Idem EffectiveFork.V)
    (B : Endofunctor.Algebra (rules a b).inference) (j : WalkingSpan) :
    foldedComponentHom a b B j = (pointwiseAlgebraIso a b j).hom ≫
      Naturality.foldHom (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b) (componentAlgebra a b B j) :=
  (pointwiseInitial a b j).hom_ext _ _

theorem foldedComponent_eq_native (a b : Idem EffectiveFork.V)
    (B : Endofunctor.Algebra (rules a b).inference) (j : WalkingSpan) :
    foldedComponent a b B j = (componentProofIso a b j).hom ≫
      Naturality.fold (componentSupport j a) (componentSupport j b)
        (componentSupport_re j a) (componentSupport_re j b) (componentAlgebra a b B j) :=
  congrArg (fun h => h.f.left) (foldedComponentHom_eq_native a b B j)
end CategoricalEssentialIncompleteness.V46.ForkDerivation
