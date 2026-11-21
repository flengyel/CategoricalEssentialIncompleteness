/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.InternalLattices
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Internal bounded distributive lattices in types

A bounded distributive lattice determines an internal lattice in `Type`: each set of
generalized elements has pointwise lattice operations. A bounded lattice homomorphism
induces an internal lattice homomorphism; its underlying morphism is monic precisely
when the original function is injective.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u

open CategoryTheory

namespace CategoricalEssentialIncompleteness

/-- The pointwise distributive lattice on morphisms of types. -/
@[instance_reducible] def typeHomDistribLattice (T A : Type u) [DistribLattice A] :
    DistribLattice (T ⟶ A) :=
  TypeCat.homEquiv.distribLattice

attribute [local instance] typeHomDistribLattice

/-- The pointwise bounds on morphisms of types. -/
@[instance_reducible] def typeHomBoundedOrder (T A : Type u) [DistribLattice A] [BoundedOrder A] :
    BoundedOrder (T ⟶ A) where
  bot := TypeCat.ofHom fun _ => ⊥
  bot_le := fun _ _ => bot_le
  top := TypeCat.ofHom fun _ => ⊤
  le_top := fun _ _ => le_top

attribute [local instance] typeHomBoundedOrder

@[simp] theorem typeHom_inf_apply {T A : Type u} [DistribLattice A]
    (a b : T ⟶ A) (t : T) : (a ⊓ b) t = a t ⊓ b t := rfl

@[simp] theorem typeHom_sup_apply {T A : Type u} [DistribLattice A]
    (a b : T ⟶ A) (t : T) : (a ⊔ b) t = a t ⊔ b t := rfl

@[simp] theorem typeHom_bot_apply {T A : Type u} [DistribLattice A] [BoundedOrder A]
    (t : T) : (⊥ : T ⟶ A) t = ⊥ := rfl

@[simp] theorem typeHom_top_apply {T A : Type u} [DistribLattice A] [BoundedOrder A]
    (t : T) : (⊤ : T ⟶ A) t = ⊤ := rfl

theorem typeHom_le_iff {T A : Type u} [DistribLattice A] (a b : T ⟶ A) :
    a ≤ b ↔ ∀ t, a t ≤ b t := Iff.rfl

/-- A bounded distributive lattice as an internal lattice in `Type`. -/
def typeLattice (A : Type u) [DistribLattice A] [BoundedOrder A] :
    InternalLattice (Type u) where
  obj := A
  lattice T := typeHomDistribLattice T A
  bounds T := typeHomBoundedOrder T A
  precomp k :=
    { toFun := fun a => k ≫ a
      map_inf' := fun _ _ => rfl
      map_sup' := fun _ _ => rfl
      map_bot' := rfl
      map_top' := rfl }
  precomp_apply _ _ := rfl

@[simp] theorem typeLattice_precomp_apply {T T' A : Type u}
    [DistribLattice A] [BoundedOrder A] (k : T' ⟶ T) (a : T ⟶ A) :
    (typeLattice A).precomp k a = k ≫ a := rfl

@[simp] theorem typeLattice_precomp_eval {T T' A : Type u}
    [DistribLattice A] [BoundedOrder A] (k : T' ⟶ T) (a : T ⟶ A) (t : T') :
    (typeLattice A).precomp k a t = a (k t) := rfl

/-- A bounded lattice homomorphism as an internal lattice homomorphism in `Type`. -/
def typeLatticeHom {A B : Type u} [DistribLattice A] [BoundedOrder A]
    [DistribLattice B] [BoundedOrder B] (f : BoundedLatticeHom A B) :
    InternalLatticeHom (typeLattice A) (typeLattice B) where
  hom := TypeCat.ofHom f
  postcomp _ :=
    { toFun := fun a => a ≫ TypeCat.ofHom f
      map_inf' := by
        intro a b
        ext t
        change f (a t ⊓ b t) = f (a t) ⊓ f (b t)
        exact f.map_inf' (a t) (b t)
      map_sup' := by
        intro a b
        ext t
        change f (a t ⊔ b t) = f (a t) ⊔ f (b t)
        exact f.map_sup' (a t) (b t)
      map_bot' := by ext t; change f ⊥ = ⊥; exact map_bot f
      map_top' := by ext t; change f ⊤ = ⊤; exact map_top f }
  postcomp_apply _ _ := rfl

@[simp] theorem typeLatticeHom_hom_apply {A B : Type u} [DistribLattice A] [BoundedOrder A]
    [DistribLattice B] [BoundedOrder B] (f : BoundedLatticeHom A B) (a : A) :
    (typeLatticeHom f).hom a = f a := rfl

@[simp] theorem typeLatticeHom_postcomp_apply {T A B : Type u}
    [DistribLattice A] [BoundedOrder A] [DistribLattice B] [BoundedOrder B]
    (f : BoundedLatticeHom A B) (a : T ⟶ A) :
    (typeLatticeHom f).postcomp T a = a ≫ TypeCat.ofHom f := rfl

@[simp] theorem typeLatticeHom_postcomp_eval {T A B : Type u}
    [DistribLattice A] [BoundedOrder A] [DistribLattice B] [BoundedOrder B]
    (f : BoundedLatticeHom A B) (a : T ⟶ A) (t : T) :
    (typeLatticeHom f).postcomp T a t = f (a t) := rfl

/-- Monicity of the induced internal map is equivalent to injectivity. -/
theorem typeLatticeHom_mono_iff_injective {A B : Type u}
    [DistribLattice A] [BoundedOrder A] [DistribLattice B] [BoundedOrder B]
    (f : BoundedLatticeHom A B) :
    Mono (typeLatticeHom f).hom ↔ Function.Injective f :=
  ofHom_mono_iff_injective f

theorem typeLatticeHom_mono {A B : Type u}
    [DistribLattice A] [BoundedOrder A] [DistribLattice B] [BoundedOrder B]
    (f : BoundedLatticeHom A B) (hf : Function.Injective f) :
    Mono (typeLatticeHom f).hom :=
  (typeLatticeHom_mono_iff_injective f).mpr hf

end CategoricalEssentialIncompleteness
