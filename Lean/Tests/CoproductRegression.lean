/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import PCats.Coproducts

/-!
# Coproduct API regression tests

Signature guards for the restriction/coproduct lemmas that
`RiceShapiro.LocalConnectedness` consumes. There is no mathematical content
here: every declaration is an `example` whose only job is to stop elaborating
if a protected signature changes.

Each lemma is pinned twice, because the two forms catch different drift.

* The `@`-ascription fixes the whole telescope: argument order, argument count,
  and the types. For `coprod_map_zero` it also fixes the *absence* of
  `[PCategoryStruct C]` and `[PCategory C]`, which the `omit` in
  `PCats.Coproducts` removes; restoring them breaks this file.
* The applied form fixes the call shape, so moving an argument between explicit
  and implicit breaks it even where the ascription would still elaborate.

`autoImplicit` is off. `lake env lean` does not apply the package's
`leanOptions`, so without this a mistyped identifier would be silently accepted
as an auto-bound implicit and the guard would pass vacuously.

Run by `scripts/syncpcats.sh`. These files sit outside the `PCats` and
`RiceShapiro` libraries and are not part of `lake build`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open PCategoryStruct CoprodStruct

/-! ### `HasCoproducts.rst_copair` -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [CoprodStruct C] [HasCoproducts C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z),
    rst (copair f g) = coprod_map (rst f) (rst g) :=
  @HasCoproducts.rst_copair

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [CoprodStruct C] [HasCoproducts C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    rst (copair f g) = coprod_map (rst f) (rst g) :=
  HasCoproducts.rst_copair f g

/-! ### `HasCoproducts.rst_coprod_map_self` -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [CoprodStruct C] [HasCoproducts C] {X : C} (f g : X ⟶ X),
    rst (coprod_map f g) = coprod_map (rst f) (rst g) :=
  @HasCoproducts.rst_coprod_map_self

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    [CoprodStruct C] [HasCoproducts C] {X : C} (f g : X ⟶ X) :
    rst (coprod_map f g) = coprod_map (rst f) (rst g) :=
  HasCoproducts.rst_coprod_map_self f g

/-! ### `HasCoproducts.coprod_map_zero`

Stated without `[PCategoryStruct C]` and `[PCategory C]`: the coproduct of two
zero morphisms is zero for reasons that do not touch the restriction structure.
-/

example : ∀ {C : Type u} [Category.{v} C] [CoprodStruct C] [HasCoproducts C]
    [Limits.HasZeroMorphisms C] {X Y : C},
    coprod_map (0 : X ⟶ X) (0 : Y ⟶ Y) = (0 : coprod X Y ⟶ coprod X Y) :=
  @HasCoproducts.coprod_map_zero

example {C : Type u} [Category.{v} C] [CoprodStruct C] [HasCoproducts C]
    [Limits.HasZeroMorphisms C] {X Y : C} :
    coprod_map (0 : X ⟶ X) (0 : Y ⟶ Y) = (0 : coprod X Y ⟶ coprod X Y) :=
  HasCoproducts.coprod_map_zero

end CategoryTheory
