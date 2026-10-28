/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.InternalLattices

/-!
# The internal total-arrow and predicate structures

All operations are morphisms in the base. Their equations are stated at every
parameter object, so they do not require the terminal object to be a generator.
This is the total-arrow reduct needed by the internal diagonal argument.
`EnrichedTotals` constructs it from enriched restriction hom-objects, and
`EnrichedDomains` constructs its domain-predicate action.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe v u w
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness

/-- Internal hom-objects with identities, composition, and chosen binary products. -/
structure InternalHom (V : Type u) [Category.{v} V] [HasFiniteLimits V] (O : Type w) where
  hom : O → O → V
  unit : ∀ X, ⊤_ V ⟶ hom X X
  composition : ∀ X Y Z, hom X Y ⨯ hom Y Z ⟶ hom X Z
  product : O → O → O
  first : ∀ X Y, ⊤_ V ⟶ hom (product X Y) X
  second : ∀ X Y, ⊤_ V ⟶ hom (product X Y) Y
  pairing : ∀ X Y Z, hom X Y ⨯ hom X Z ⟶ hom X (product Y Z)

namespace InternalHom
variable {V : Type u} [Category.{v} V] [HasFiniteLimits V] {O : Type w}
variable (H : InternalHom V O)

def identity {T : V} (X : O) : T ⟶ H.hom X X := terminal.from T ≫ H.unit X
def comp {T : V} {X Y Z : O} (f : T ⟶ H.hom X Y) (g : T ⟶ H.hom Y Z) :
    T ⟶ H.hom X Z := prod.lift f g ≫ H.composition X Y Z
def pair {T : V} {X Y Z : O} (f : T ⟶ H.hom X Y) (g : T ⟶ H.hom X Z) :
    T ⟶ H.hom X (H.product Y Z) := prod.lift f g ≫ H.pairing X Y Z
def fst {T : V} (X Y : O) : T ⟶ H.hom (H.product X Y) X :=
  terminal.from T ≫ H.first X Y
def snd {T : V} (X Y : O) : T ⟶ H.hom (H.product X Y) Y :=
  terminal.from T ≫ H.second X Y

/-- The ordinary category and binary-product equations, at arbitrary parameters. -/
class CartesianLaws : Prop where
  assoc : ∀ {T X Y Z W} (f : T ⟶ H.hom X Y) (g : T ⟶ H.hom Y Z)
    (h : T ⟶ H.hom Z W), H.comp (H.comp f g) h = H.comp f (H.comp g h)
  id_comp : ∀ {T X Y} (f : T ⟶ H.hom X Y), H.comp (H.identity X) f = f
  comp_id : ∀ {T X Y} (f : T ⟶ H.hom X Y), H.comp f (H.identity Y) = f
  pair_fst : ∀ {T X Y Z} (f : T ⟶ H.hom X Y) (g : T ⟶ H.hom X Z),
    H.comp (H.pair f g) (H.fst Y Z) = f
  pair_snd : ∀ {T X Y Z} (f : T ⟶ H.hom X Y) (g : T ⟶ H.hom X Z),
    H.comp (H.pair f g) (H.snd Y Z) = g
  pair_eta : ∀ {T X Y Z} (f : T ⟶ H.hom X (H.product Y Z)),
    H.pair (H.comp f (H.fst Y Z)) (H.comp f (H.snd Y Z)) = f

@[simp] theorem precomp_identity {T T' : V} (k : T' ⟶ T) (X : O) :
    k ≫ H.identity X = H.identity X := by simp [identity]
@[simp] theorem precomp_fst {T T' : V} (k : T' ⟶ T) (X Y : O) :
    k ≫ H.fst X Y = H.fst X Y := by simp [fst]
@[simp] theorem precomp_snd {T T' : V} (k : T' ⟶ T) (X Y : O) :
    k ≫ H.snd X Y = H.snd X Y := by simp [snd]
@[simp] theorem precomp_comp {T T' : V} (k : T' ⟶ T) {X Y Z : O}
    (f : T ⟶ H.hom X Y) (g : T ⟶ H.hom Y Z) :
    k ≫ H.comp f g = H.comp (k ≫ f) (k ≫ g) := by simp [comp, ← Category.assoc, prod.comp_lift]
@[simp] theorem precomp_pair {T T' : V} (k : T' ⟶ T) {X Y Z : O}
    (f : T ⟶ H.hom X Y) (g : T ⟶ H.hom X Z) :
    k ≫ H.pair f g = H.pair (k ≫ f) (k ≫ g) := by simp [pair, ← Category.assoc, prod.comp_lift]

variable [H.CartesianLaws]
attribute [simp] CartesianLaws.id_comp CartesianLaws.comp_id
  CartesianLaws.pair_fst CartesianLaws.pair_snd

theorem hom_ext {T : V} {X Y Z : O} {f g : T ⟶ H.hom X (H.product Y Z)}
    (hf : H.comp f (H.fst Y Z) = H.comp g (H.fst Y Z))
    (hs : H.comp f (H.snd Y Z) = H.comp g (H.snd Y Z)) : f = g := by
  rw [← CartesianLaws.pair_eta f, ← CartesianLaws.pair_eta g, hf, hs]

@[simp] theorem comp_pair {T : V} {X Y Z W : O} (f : T ⟶ H.hom X Y)
    (g : T ⟶ H.hom Y Z) (h : T ⟶ H.hom Y W) :
    H.comp f (H.pair g h) = H.pair (H.comp f g) (H.comp f h) := by
  apply H.hom_ext <;> simp [CartesianLaws.assoc]

end InternalHom

/-- Internal predicate lattices with a contravariant action of the hom-objects. -/
structure InternalPredicates {V : Type u} [Category.{v} V] [HasFiniteLimits V]
    {O : Type w} (H : InternalHom V O) where
  lattice : O → InternalLattice V
  action : ∀ X Y, H.hom X Y ⨯ (lattice Y).obj ⟶ (lattice X).obj
  pull : ∀ {T X Y}, (T ⟶ H.hom X Y) →
    BoundedLatticeHom (T ⟶ (lattice Y).obj) (T ⟶ (lattice X).obj)
  pull_apply : ∀ {T X Y} (f : T ⟶ H.hom X Y) (a : T ⟶ (lattice Y).obj),
    pull f a = prod.lift f a ≫ action X Y
  pull_id : ∀ {T X} (a : T ⟶ (lattice X).obj), pull (H.identity X) a = a
  pull_comp : ∀ {T X Y Z} (f : T ⟶ H.hom X Y) (g : T ⟶ H.hom Y Z)
    (a : T ⟶ (lattice Z).obj), pull (H.comp f g) a = pull f (pull g a)

namespace InternalPredicates
variable {V : Type u} [Category.{v} V] [HasFiniteLimits V] {O : Type w}
variable {H : InternalHom V O} (P : InternalPredicates H)

@[simp] theorem precomp_pull {T T' : V} (k : T' ⟶ T) {X Y : O}
    (f : T ⟶ H.hom X Y) (a : T ⟶ (P.lattice Y).obj) :
    k ≫ P.pull f a = P.pull (k ≫ f) (k ≫ a) := by
  simp [P.pull_apply, ← Category.assoc, prod.comp_lift]

end InternalPredicates

/-- A monic internal bounded lattice map, natural for all total-arrow families. -/
structure InternalPredicateEmbedding {V : Type u} [Category.{v} V] [HasFiniteLimits V]
    {O : Type w} {H : InternalHom V O} (E P : InternalPredicates H) where
  app : ∀ X, InternalLatticeHom (E.lattice X) (P.lattice X)
  mono : ∀ X, Mono (app X).hom
  naturality : ∀ {T X Y} (f : T ⟶ H.hom X Y) (e : T ⟶ (E.lattice Y).obj),
    P.pull f (e ≫ (app Y).hom) = E.pull f e ≫ (app X).hom

namespace InternalPredicateEmbedding
variable {V : Type u} [Category.{v} V] [HasFiniteLimits V] {O : Type w}
variable {H : InternalHom V O} {E P : InternalPredicates H}
variable (j : InternalPredicateEmbedding E P)

theorem injective (T : V) (X : O) : Function.Injective ((j.app X).postcomp T) := by
  let := j.mono X
  intro a b h
  apply (cancel_mono (j.app X).hom).mp
  simpa only [InternalLatticeHom.postcomp_apply] using h

end InternalPredicateEmbedding
end CategoricalEssentialIncompleteness
