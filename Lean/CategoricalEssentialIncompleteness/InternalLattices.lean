/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.ParameterizedEqualizer

/-!
# Internal bounded distributive lattices and complementary pairs

The representable functor of an internal lattice carries bounded distributive
lattice structures naturally under precomposition. The object of complementary pairs
is defined by the pullback in `eq:v8-complement-pullback`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness

/-- A bounded distributive lattice object described on all generalized elements. -/
structure InternalLattice (V : Type u) [Category.{v} V] where
  obj : V
  lattice : ∀ T : V, DistribLattice (T ⟶ obj)
  bounds : ∀ T : V, BoundedOrder (T ⟶ obj)
  precomp : ∀ {T T' : V}, (T' ⟶ T) → BoundedLatticeHom (T ⟶ obj) (T' ⟶ obj)
  precomp_apply : ∀ {T T' : V} (k : T' ⟶ T) (a : T ⟶ obj), precomp k a = k ≫ a

attribute [instance] InternalLattice.lattice InternalLattice.bounds

/-- An internal bounded lattice homomorphism, with its action on generalized elements. -/
structure InternalLatticeHom {V : Type u} [Category.{v} V] (L M : InternalLattice V) where
  hom : L.obj ⟶ M.obj
  postcomp : ∀ T : V, BoundedLatticeHom (T ⟶ L.obj) (T ⟶ M.obj)
  postcomp_apply : ∀ T (a : T ⟶ L.obj), postcomp T a = a ≫ hom

namespace InternalLattice

variable {V : Type u} [Category.{v} V] (L : InternalLattice V)

@[simp]
theorem comp_inf {T T' : V} (k : T' ⟶ T) (a b : T ⟶ L.obj) :
    k ≫ (a ⊓ b) = (k ≫ a) ⊓ (k ≫ b) := by
  rw [← L.precomp_apply, map_inf, L.precomp_apply, L.precomp_apply]

@[simp]
theorem comp_sup {T T' : V} (k : T' ⟶ T) (a b : T ⟶ L.obj) :
    k ≫ (a ⊔ b) = (k ≫ a) ⊔ (k ≫ b) := by
  rw [← L.precomp_apply, map_sup, L.precomp_apply, L.precomp_apply]

@[simp]
theorem comp_bot {T T' : V} (k : T' ⟶ T) : k ≫ (⊥ : T ⟶ L.obj) = ⊥ := by
  rw [← L.precomp_apply, map_bot]

@[simp]
theorem comp_top {T T' : V} (k : T' ⟶ T) : k ≫ (⊤ : T ⟶ L.obj) = ⊤ := by
  rw [← L.precomp_apply, map_top]

variable [HasFiniteLimits V]

/-- The representing arrow of meet. -/
def meet : L.obj ⨯ L.obj ⟶ L.obj := prod.fst ⊓ prod.snd

/-- The representing arrow of join. -/
def join : L.obj ⨯ L.obj ⟶ L.obj := prod.fst ⊔ prod.snd

@[simp]
theorem lift_meet {T : V} (a b : T ⟶ L.obj) : prod.lift a b ≫ L.meet = a ⊓ b := by
  simp [meet]

@[simp]
theorem lift_join {T : V} (a b : T ⟶ L.obj) : prod.lift a b ≫ L.join = a ⊔ b := by
  simp [join]

/-- The arrow sending a pair to its meet and join. -/
def meetJoin : L.obj ⨯ L.obj ⟶ L.obj ⨯ L.obj := prod.lift L.meet L.join

/-- The pair of global bounds. -/
def boundPair : ⊤_ V ⟶ L.obj ⨯ L.obj := prod.lift ⊥ ⊤

/-- The complementary-pair pullback of `eq:v8-complement-pullback`. -/
def Complements : V := pullback L.meetJoin L.boundPair

def complementPos : L.Complements ⟶ L.obj := pullback.fst _ _ ≫ prod.fst
def complementNeg : L.Complements ⟶ L.obj := pullback.fst _ _ ≫ prod.snd

/-- The two universal projections are complementary as generalized elements. -/
theorem complement_isCompl : IsCompl L.complementPos L.complementNeg := by
  have h := pullback.condition (f := L.meetJoin) (g := L.boundPair)
  have hm := congrArg (fun k ↦ k ≫ prod.fst) h
  have hj := congrArg (fun k ↦ k ≫ prod.snd) h
  apply IsCompl.of_eq
  · simpa [meetJoin, boundPair, meet, complementPos, complementNeg, Category.assoc] using hm
  · simpa [meetJoin, boundPair, join, complementPos, complementNeg, Category.assoc] using hj

/-- Any complementary pair at an arbitrary parameter lifts to the internal pair object. -/
def liftComplement {T : V} (a : ComplementaryPair (T ⟶ L.obj)) : T ⟶ L.Complements :=
  pullback.lift (prod.lift a.pos a.neg) (terminal.from T) (by
    apply prod.hom_ext
    · simpa [meetJoin, boundPair, Category.assoc] using a.compl.inf_eq_bot
    · simpa [meetJoin, boundPair, Category.assoc] using a.compl.sup_eq_top)

@[simp, reassoc]
theorem liftComplement_pos {T : V} (a : ComplementaryPair (T ⟶ L.obj)) :
    L.liftComplement a ≫ L.complementPos = a.pos := by
  simp [liftComplement, complementPos]

@[simp, reassoc]
theorem liftComplement_neg {T : V} (a : ComplementaryPair (T ⟶ L.obj)) :
    L.liftComplement a ≫ L.complementNeg = a.neg := by
  simp [liftComplement, complementNeg]

/-- Generalized points of the pair object give complementary pairs. -/
def complementPair {T : V} (f : T ⟶ L.Complements) : ComplementaryPair (T ⟶ L.obj) :=
  (⟨L.complementPos, L.complementNeg, L.complement_isCompl⟩ :
    ComplementaryPair (L.Complements ⟶ L.obj)).map (L.precomp f)

@[simp]
theorem complementPair_pos {T : V} (f : T ⟶ L.Complements) :
    (L.complementPair f).pos = f ≫ L.complementPos := L.precomp_apply _ _

@[simp]
theorem complementPair_neg {T : V} (f : T ⟶ L.Complements) :
    (L.complementPair f).neg = f ≫ L.complementNeg := L.precomp_apply _ _

/-- The finite-limit lift is inverse to taking the two projections. -/
theorem liftComplement_pair {T : V} (f : T ⟶ L.Complements) :
    L.liftComplement (L.complementPair f) = f := by
  apply pullback.hom_ext
  · apply prod.hom_ext <;> simp [liftComplement, complementPos, complementNeg, Category.assoc]
  · exact terminalIsTerminal.hom_ext _ _

end InternalLattice

end CategoricalEssentialIncompleteness
