/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PartialMapFunctor

/-! # Pullback-preserving functors act on monic partial spans -/

@[expose] public section

noncomputable section

universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.V46.PartialMaps

variable {D : Type u₁} [Category.{v₁} D] [HasPullbacks D]
variable {E : Type u₂} [Category.{v₂} E] [HasPullbacks E]
variable (F : D ⥤ E) [F.PreservesMonomorphisms]
variable [PreservesLimitsOfShape WalkingCospan F]

example : Par D ⥤ Par E := inducedFunctor F

example {X Y : Par D} (f : X ⟶ Y) :
    (inducedFunctor F).map (rst f) = rst ((inducedFunctor F).map f) :=
  inducedFunctor_restriction F f

example {X Y : Par D} (f : X ⟶ Y) (hf : isTotal f) :
    isTotal ((inducedFunctor F).map f) := inducedFunctor_total F f hf

example {X Y : Par D} (m : X.obj ⟶ Y.obj) [Mono m] :
    (inducedFunctor F).map (ofTotal m) = ofTotal (F.map m) ∧
      (inducedFunctor F).map (inverseMono m) = inverseMono (F.map m) :=
  ⟨inducedFunctor_ofTotal F m, inducedFunctor_inverseMono F m⟩

#print axioms CategoricalEssentialIncompleteness.V46.PartialMaps.inducedFunctor
#print axioms CategoricalEssentialIncompleteness.V46.PartialMaps.inducedFunctor_restriction
#print axioms CategoricalEssentialIncompleteness.V46.PartialMaps.inducedFunctor_total
#print axioms CategoricalEssentialIncompleteness.V46.PartialMaps.inducedFunctor_ofTotal
#print axioms CategoricalEssentialIncompleteness.V46.PartialMaps.inducedFunctor_inverseMono
