/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerCategoryCoproducts


/-! # Tagged restriction coproducts with one common oracle program -/

@[expose] public section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.CoprodStruct
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Uniform
variable {z : Family}
attribute [instance 2000] nativeRestriction

example : CoprodStruct (Object z) := inferInstance
example : CategoryTheory.HasCoproducts (Object z) := inferInstance
example : RestrictionCoproducts (Object z) := inferInstance
example (X Y : Object z) : carrier z (coproduct X Y) = (carrier z X ⊕ carrier z Y) := rfl
example (X Y : Object z) : (i0 X Y).val = fun x => Part.some (Sum.inl x) := i0_val X Y
example (X Y : Object z) : (i1 X Y).val = fun x => Part.some (Sum.inr x) := i1_val X Y
example {X Y Z : Object z} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (copairRaw f g).val = Sum.elim f.val g.val := rfl
example {W X Y Z : Object z} (f : W ⟶ X) (g : Y ⟶ Z) :
    (sumMap f g).val = PartialFunctions.sumMap f.val g.val := sumMap_val f g
end CategoricalEssentialIncompleteness.V46.Miller.Uniform
