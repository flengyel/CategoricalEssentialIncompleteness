/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import PCats.DomSubdomains

/-!
# Signature guards for subdomain composition and inverse images

Each `example` fails to elaborate if a protected signature or equation changes.
Exact `@`-ascriptions pin the telescopes of `Dom.Subdomain`, `Subdomain.toDom`,
`Subdomain.inclusion`, `Subdomain.compose`, `Subdomain.inverseImage`,
`Subdomain.inverseImageMap`, and `Subdomain.inverseImage_existsUnique`; applied
examples guard the remaining declarations and the defining equations. These
guards fail if a range, zero-morphism, choice, prodominical, or isotype premise
enters a protected declaration. Classical axiom dependencies are checked
separately by `check_axioms.lean`.

`autoImplicit` is off: `lake env lean` does not apply the package's
`leanOptions`, and an unbound identifier would otherwise be auto-bound and the
guard would hold vacuously.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe v u

namespace CategoryTheory

open PCategoryStruct

#check @Dom.Subdomain
#check @Dom.Subdomain.toDom
#check @Dom.Subdomain.inclusion
#check @Dom.Subdomain.compose
#check @Dom.Subdomain.compose_inclusion
#check @Dom.Subdomain.inverseImage
#check @Dom.Subdomain.inverseImageMap
#check @Dom.Subdomain.inverseImage_existsUnique

/-! ### Subdomains and their domain objects -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C],
    Dom C → Type v :=
  @Dom.Subdomain

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A : Dom C}, Dom.Subdomain A → Dom C :=
  @Dom.Subdomain.toDom

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A : Dom C} (s : Dom.Subdomain A) : s.toDom.base = A.base :=
  Dom.Subdomain.toDom_base s

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A : Dom C} (s : Dom.Subdomain A) : s.toDom.idem = s.idem :=
  Dom.Subdomain.toDom_idem s

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A : Dom C} (s : Dom.Subdomain A) :
    s.idem ≫ s.idem = s.idem :=
  Dom.Subdomain.idem_comp_idem s

/-! ### The inclusion and its monomorphism property -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A : Dom C} (s : Dom.Subdomain A), s.toDom ⟶ A :=
  @Dom.Subdomain.inclusion

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A : Dom C} (s : Dom.Subdomain A) : s.inclusion.hom = s.idem :=
  Dom.Subdomain.inclusion_hom s

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A : Dom C} (s : Dom.Subdomain A) : Mono s.inclusion :=
  Dom.Subdomain.inclusion_mono s

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A : Dom C} (s : Dom.Subdomain A) {W : Dom C} (f g : W ⟶ s.toDom)
    (h : f ≫ s.inclusion = g ≫ s.inclusion) : f = g :=
  (Dom.Subdomain.inclusion_mono s).right_cancellation f g h

/-! ### Closure under composition -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A : Dom C} (s : Dom.Subdomain A),
    Dom.Subdomain s.toDom → Dom.Subdomain A :=
  @Dom.Subdomain.compose

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A : Dom C} (s : Dom.Subdomain A) (t : Dom.Subdomain s.toDom) :
    (s.compose t).idem = t.idem :=
  Dom.Subdomain.compose_idem s t

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A : Dom C} (s : Dom.Subdomain A) (t : Dom.Subdomain s.toDom) :
    (s.compose t).toDom = t.toDom :=
  Dom.Subdomain.compose_toDom s t

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A : Dom C} (s : Dom.Subdomain A) (t : Dom.Subdomain s.toDom) :
    (s.compose t).inclusion.hom = t.idem :=
  Dom.Subdomain.inclusion_hom (s.compose t)

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A : Dom C} (s : Dom.Subdomain A) (t : Dom.Subdomain s.toDom) :
    (s.compose t).inclusion = t.inclusion ≫ s.inclusion :=
  Dom.Subdomain.compose_inclusion s t

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A : Dom C} (s : Dom.Subdomain A) (t : Dom.Subdomain s.toDom) :
    Mono (s.compose t).inclusion :=
  Dom.Subdomain.inclusion_mono (s.compose t)

/-! ### The inverse image -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A B : Dom C} (_s : Dom.Subdomain B), (A ⟶ B) → Dom.Subdomain A :=
  @Dom.Subdomain.inverseImage

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A B : Dom C} (s : Dom.Subdomain B) (θ : A ⟶ B) :
    (s.inverseImage θ).idem = rst (θ.hom ≫ s.idem) :=
  Dom.Subdomain.inverseImage_idem s θ

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A B : Dom C} (s : Dom.Subdomain B) (θ : A ⟶ B) :
    (s.inverseImage θ).inclusion.hom = rst (θ.hom ≫ s.idem) :=
  Dom.Subdomain.inclusion_hom (s.inverseImage θ)

/-! ### The upper arrow and the commuting square -/

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A B : Dom C} (s : Dom.Subdomain B) (θ : A ⟶ B),
    (s.inverseImage θ).toDom ⟶ s.toDom :=
  @Dom.Subdomain.inverseImageMap

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A B : Dom C} (s : Dom.Subdomain B) (θ : A ⟶ B) :
    (s.inverseImageMap θ).hom = θ.hom ≫ s.idem :=
  Dom.Subdomain.inverseImageMap_hom s θ

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A B : Dom C} (s : Dom.Subdomain B) (θ : A ⟶ B) :
    s.inverseImageMap θ ≫ s.inclusion
      = (s.inverseImage θ).inclusion ≫ θ :=
  Dom.Subdomain.inverseImage_comm s θ

/-! ### The lift and the universal property -/

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A B : Dom C} (s : Dom.Subdomain B) (θ : A ⟶ B) {W : Dom C}
    (γ : W ⟶ s.toDom) (β : W ⟶ A) (hcomm : γ ≫ s.inclusion = β ≫ θ) :
    (s.inverseImageLift θ γ β hcomm).hom = β.hom :=
  Dom.Subdomain.inverseImageLift_hom s θ γ β hcomm

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A B : Dom C} (s : Dom.Subdomain B) (θ : A ⟶ B) {W : Dom C}
    (γ : W ⟶ s.toDom) (β : W ⟶ A) (hcomm : γ ≫ s.inclusion = β ≫ θ) :
    s.inverseImageLift θ γ β hcomm ≫ s.inverseImageMap θ = γ :=
  Dom.Subdomain.inverseImageLift_map s θ γ β hcomm

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A B : Dom C} (s : Dom.Subdomain B) (θ : A ⟶ B) {W : Dom C}
    (γ : W ⟶ s.toDom) (β : W ⟶ A) (hcomm : γ ≫ s.inclusion = β ≫ θ) :
    s.inverseImageLift θ γ β hcomm ≫ (s.inverseImage θ).inclusion = β :=
  Dom.Subdomain.inverseImageLift_inclusion s θ γ β hcomm

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A B : Dom C} (s : Dom.Subdomain B) (θ : A ⟶ B) {W : Dom C}
    (γ : W ⟶ s.toDom) (β : W ⟶ A) (hcomm : γ ≫ s.inclusion = β ≫ θ)
    (l : W ⟶ (s.inverseImage θ).toDom)
    (hl : l ≫ (s.inverseImage θ).inclusion = β) :
    l = s.inverseImageLift θ γ β hcomm :=
  Dom.Subdomain.inverseImageLift_unique s θ γ β hcomm l hl

example : ∀ {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A B : Dom C} (s : Dom.Subdomain B) (θ : A ⟶ B) {W : Dom C}
    (γ : W ⟶ s.toDom) (β : W ⟶ A), γ ≫ s.inclusion = β ≫ θ →
    ∃! l : W ⟶ (s.inverseImage θ).toDom,
      l ≫ s.inverseImageMap θ = γ ∧
        l ≫ (s.inverseImage θ).inclusion = β :=
  @Dom.Subdomain.inverseImage_existsUnique

example {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C]
    {A B : Dom C} (s : Dom.Subdomain B) (θ : A ⟶ B) {W : Dom C}
    (γ : W ⟶ s.toDom) (β : W ⟶ A) (hcomm : γ ≫ s.inclusion = β ≫ θ) :
    ∃! l : W ⟶ (s.inverseImage θ).toDom,
      l ≫ s.inverseImageMap θ = γ ∧
        l ≫ (s.inverseImage θ).inclusion = β :=
  Dom.Subdomain.inverseImage_existsUnique s θ γ β hcomm

end CategoryTheory
