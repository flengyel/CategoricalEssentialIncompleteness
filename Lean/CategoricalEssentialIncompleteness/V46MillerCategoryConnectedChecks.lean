/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCategoryConnected


/-! # Connected points, finite domain joins and uniform partial inverses -/

@[expose] public section
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Uniform
variable {z : Family}
attribute [instance 2000] nativeRestriction

example : BinaryJoins (Object z) := inferInstance
example : JoinInverse (Object z) := inferInstance
example : LocallyConnected (Object z) := inferInstance
example : WeakChoice (Object z) := inferInstance
example (X : Object z) (x : carrier z X) : Connected (singletonIdem X x) := singleton_connected X x
example {X : Object z} (a b : Idem X) : a ≤ b ↔ support a ⊆ support b := support_le_iff a b
example {X Y : Object z} (f : X ⟶ Y) (hf : PartialMono f) :
    ∀ x x' y,y ∈ f.val x → y ∈ f.val x' → x = x' := injective_of_partialMono f hf
example {X Y : Object z} (f : X ⟶ Y) (hf : Injective f) (x : carrier z X) (y : carrier z Y) :
    x ∈ (inverse f hf).val y ↔ y ∈ f.val x := inverse_graph f hf y x
example {X Y : Object z} (f : X ⟶ Y) (hf : Injective f) :
    inverse f hf ≫ f = rst (inverse f hf) := (inverse_isSection f hf).comp
example {X Y : Object z} (f : X ⟶ Y) (hf : Injective f) :
    f ≫ inverse f hf ≫ f = f := (inverse_isSection f hf).receives
example {X Y : Object z} (f : X ⟶ Y) (hf : PartialMono f) :
    ∃ s : Y ⟶ X,s ≫ f = rst s ∧ f ≫ s ≫ f = f :=
  ⟨inverse f (injective_of_partialMono f hf),
    (inverse_isSection f (injective_of_partialMono f hf)).comp,
    (inverse_isSection f (injective_of_partialMono f hf)).receives⟩
end CategoricalEssentialIncompleteness.V46.Miller.Uniform
