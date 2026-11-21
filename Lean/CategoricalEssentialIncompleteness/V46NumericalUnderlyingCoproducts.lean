/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46NumericalUnderlying
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-! # Finite coproducts on the numerical carriers -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness.V46.NumericalUnderlying

def emptyObject : NumericalTuples.Object := ⟨1,∅,REPred.const False⟩

instance initialCarrierEmpty : IsEmpty (NumericalTuples.Point (⊥_ NumericalTuples.Object)) where
  false x := ((initial.to emptyObject).toFun x).property

def initialCarrierInitial : IsInitial (functor.obj (⊥_ NumericalTuples.Object)) := by
  change IsInitial (NumericalTuples.Point (⊥_ NumericalTuples.Object))
  exact ((Types.initial_iff_empty _).mpr initialCarrierEmpty).some

instance preservesInitial : PreservesColimit (Functor.empty.{0} NumericalTuples.Object) functor :=
  preservesInitial_of_iso functor (initialIsInitial.uniqueUpToIso initialCarrierInitial)

instance preservesEmpty : PreservesColimitsOfShape (Discrete PEmpty.{1}) functor :=
  preservesColimitsOfShape_pempty_of_preservesInitial functor

instance preservesFiniteCoproducts (J : Type u) [Finite J] :
    PreservesColimitsOfShape (Discrete J) functor :=
  PreservesFiniteCoproducts.of_preserves_binary_and_initial functor J

end CategoricalEssentialIncompleteness.V46.NumericalUnderlying
