/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalSyntax
public import CategoricalEssentialIncompleteness.EnumerableUnderlyingPullbacks
public import CategoricalEssentialIncompleteness.EnumerableExtensive
public import Mathlib.CategoryTheory.Limits.Yoneda

/-! # The underlying carrier functor for numerical tuples -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.NumericalUnderlying

def functor : NumericalTuples.Object ⥤ Type where
  obj := NumericalTuples.Point
  map f := ↾f.toFun
  map_id _ := rfl
  map_comp _ _ := rfl

def comparison : functor ≅ NumericalTuples.comparison ⋙ EnumerableCarriers.underlying :=
  NatIso.ofComponents (fun C => (NumericalTuples.pointEquiv C).toIso) (by
    intro C D f
    apply ConcreteCategory.hom_ext
    intro x
    exact (NumericalTuples.comparisonMap_function f x).symm)

def terminalPoint : NumericalTuples.Point NumericalTuples.terminalObject := ⟨(), Set.mem_univ _⟩

/-- A fixed carrier point defines a computable constant morphism. -/
def point {C : NumericalTuples.Object} (x : NumericalTuples.Point C) :
    NumericalTuples.terminalObject ⟶ C where
  toFun _ := x
  represented := ⟨fun _ => Part.some x.val, (Computable.const x.val).partrec, fun _ => rfl⟩

def pointHomEquiv (C : NumericalTuples.Object) :
    NumericalTuples.Point C ≃ (NumericalTuples.terminalObject ⟶ C) where
  toFun := point
  invFun f := f.toFun terminalPoint
  left_inv _ := rfl
  right_inv f := by
    apply NumericalTuples.Map.ext
    funext x
    rcases x with ⟨x, hx⟩
    cases x
    rfl

def homComparison : functor ≅ coyoneda.obj (op NumericalTuples.terminalObject) :=
  NatIso.ofComponents (fun C => (pointHomEquiv C).toIso) (by
    intro C D f
    apply ConcreteCategory.hom_ext
    intro x
    exact NumericalTuples.Map.ext rfl)

/-- All limits that exist are computed on the carrier functions. -/
instance preservesLimits : PreservesLimits functor :=
  preservesLimits_of_natIso homComparison.symm

instance reflectsIsomorphisms : functor.ReflectsIsomorphisms :=
  reflectsIsomorphisms_of_iso comparison.symm

instance preservesBinaryCoproducts :
    PreservesColimitsOfShape (Discrete WalkingPair) functor :=
  preservesColimitsOfShape_of_natIso comparison.symm

end CategoricalEssentialIncompleteness.V46.NumericalUnderlying
