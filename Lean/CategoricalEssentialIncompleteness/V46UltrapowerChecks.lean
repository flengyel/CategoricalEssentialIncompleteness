/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46Ultrapower

/-! Explicit types for the ultrapower regularity theorem. -/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Filter
open CategoricalEssentialIncompleteness.V46

example {I : Type u} (U : Ultrafilter I) :
    PreservesFiniteLimits (Ultrapower.functor U) ∧
      PreservesFiniteCoproducts (Ultrapower.functor U) ∧
      ∀ (X Y : Type u) (f : X ⟶ Y),
        ∃ e : (Ultrapower.functor U).obj (image f) ≅
            image ((Ultrapower.functor U).map f),
          e.hom ≫ image.ι ((Ultrapower.functor U).map f) =
            (Ultrapower.functor U).map (image.ι f) :=
  Ultrapower.regular U

example {I : Type u} (U : Ultrafilter I) {X : Type u} (p : X → Prop) :
    Ultrapower.Obj U {x // p x} ≃
      {x : Ultrapower.Obj U X // Germ.LiftPred p x} :=
  Ultrapower.subtypeEquiv U p

example {I : Type u} (U : Ultrafilter I) {X Y : Type u}
    (f : X ⟶ Y) (x : I → X) :
    (Ultrapower.functor U).map f (Germ.ofFun x) =
      Germ.ofFun (fun i => f (x i)) :=
  Ultrapower.map_representative U f x

example {I : Type u} (U : Ultrafilter I) {X Y : Type u}
    (p : X → Prop) (q : Y → Prop) (f : X → Y) (hf : ∀ x, p x → q (f x))
    (x : Ultrapower.Obj U {x // p x}) :
    (Ultrapower.subtypeEquiv U q
      (Germ.map (fun a : {x // p x} => (⟨f a, hf a a.property⟩ : {y // q y})) x)).val =
      Germ.map f ((Ultrapower.subtypeEquiv U p x).val) :=
  Ultrapower.subtypeEquiv_naturality U p q f hf x
