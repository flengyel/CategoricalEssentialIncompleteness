/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46CategoricalDeletionLaws

/-! The deletion identity keeps arbitrary internal names and list parameters. -/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness CategoricalEssentialIncompleteness.V46

variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]
variable {V X : D} (L : StableListAlgebra V) (E : DecidableVariables V)

example (x y : X ⟶ V) (w : X ⟶ L.algebra.carrier) :
    prod.lift x (prod.lift y w ≫ L.deletion E) ≫ L.membership E =
      Two.binary Bool.and (Two.unary Bool.not (prod.lift x y ≫ E.test))
        (prod.lift x w ≫ L.membership E) :=
  L.membership_deletion E x y w

example :
    prod.lift (prod.fst ≫ prod.fst)
        (prod.lift (prod.fst ≫ prod.snd) prod.snd ≫ L.deletion E) ≫ L.membership E =
      Two.binary Bool.and (Two.unary Bool.not (prod.fst ≫ E.test))
        (prod.lift (prod.fst ≫ prod.fst) prod.snd ≫ L.membership E) :=
  L.membership_deletion_parameter E

example (x y z : X ⟶ V) :
    (prod.lift x y ≫ E.test) ⊓ (prod.lift x z ≫ E.test) ≤ prod.lift y z ≫ E.test :=
  E.test_common_source x y z
