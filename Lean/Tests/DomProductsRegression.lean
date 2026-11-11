/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import PCats.DomProducts

/-!
# Signature guards for binary products in `Dom C`

Each `example` fails to elaborate if a protected signature or equation
changes. Exact `@`-ascriptions pin the telescopes of `Dom.binaryProduct` and
`Dom.binaryProduct_existsUnique`; applied examples guard the remaining
declarations. These guards fail if a range, zero-morphism, choice,
prodominical, or isotype premise enters a protected declaration. Classical
axiom dependencies are checked separately by `check_axioms.lean`.

`autoImplicit` is off: `lake env lean` does not apply the package's
`leanOptions`, and an unbound identifier would otherwise be auto-bound and the
guard would hold vacuously.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open PCategoryStruct

#check @Dom.binaryProduct
#check @Dom.binaryProductFst
#check @Dom.binaryProductSnd
#check @Dom.binaryProductLift
#check @Dom.binaryProduct_existsUnique

/-! ### The product object -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C],
    Dom C → Dom C → Dom C :=
  @Dom.binaryProduct

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    (d e : Dom C) :
    (Dom.binaryProduct d e).base = nearProd d.base e.base :=
  Dom.binaryProduct_base d e

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    (d e : Dom C) :
    (Dom.binaryProduct d e).idem = nearProd_map d.idem e.idem :=
  Dom.binaryProduct_idem d e

/-! ### The projections are restricted, not the bare `p₀` and `p₁` -/

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    (d e : Dom C) :
    (Dom.binaryProductFst d e).hom
      = nearProd_map d.idem e.idem ≫ p0 d.base e.base :=
  Dom.binaryProductFst_hom d e

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    (d e : Dom C) :
    (Dom.binaryProductSnd d e).hom
      = nearProd_map d.idem e.idem ≫ p1 d.base e.base :=
  Dom.binaryProductSnd_hom d e

/-! ### The mediating morphism is the partial pairing -/

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {a d e : Dom C} (u : a ⟶ d) (v : a ⟶ e) :
    (Dom.binaryProductLift u v).hom = partialPairing u.hom v.hom :=
  Dom.binaryProductLift_hom u v

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {a d e : Dom C} (u : a ⟶ d) (v : a ⟶ e) :
    Dom.binaryProductLift u v ≫ Dom.binaryProductFst d e = u :=
  Dom.binaryProductLift_fst u v

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {a d e : Dom C} (u : a ⟶ d) (v : a ⟶ e) :
    Dom.binaryProductLift u v ≫ Dom.binaryProductSnd d e = v :=
  Dom.binaryProductLift_snd u v

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {a d e : Dom C} {u : a ⟶ d} {v : a ⟶ e}
    (m : a ⟶ Dom.binaryProduct d e)
    (hu : m ≫ Dom.binaryProductFst d e = u)
    (hv : m ≫ Dom.binaryProductSnd d e = v) :
    m = Dom.binaryProductLift u v :=
  Dom.binaryProductLift_unique m hu hv

/-! ### The direct universal property -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {a d e : Dom C} (u : a ⟶ d) (v : a ⟶ e),
    ∃! l : a ⟶ Dom.binaryProduct d e,
      l ≫ Dom.binaryProductFst d e = u ∧
        l ≫ Dom.binaryProductSnd d e = v :=
  @Dom.binaryProduct_existsUnique

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {a d e : Dom C} (u : a ⟶ d) (v : a ⟶ e) :
    ∃! l : a ⟶ Dom.binaryProduct d e,
      l ≫ Dom.binaryProductFst d e = u ∧
        l ≫ Dom.binaryProductSnd d e = v :=
  Dom.binaryProduct_existsUnique u v

end CategoryTheory
