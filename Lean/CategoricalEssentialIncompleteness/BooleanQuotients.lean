/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.Diagonal
public import Mathlib.CategoryTheory.RegularCategory.Basic
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Boolean quotients and represented bound fibers

Boolean algebras are specified on all generalized elements, naturally under
precomposition. By Yoneda this is the internal Boolean-algebra structure.
Presentations and quotients have regular epimorphisms as underlying morphisms; their
fibers are equalizer subobjects.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u w w' v' u'

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness

/-- An internal Boolean algebra, expressed by its representable Boolean-algebra functor. -/
structure BooleanObject (C : Type u') [Category.{v'} C] where
  obj : C
  algebra : ∀ X : C, BooleanAlgebra (X ⟶ obj)
  precomp : ∀ {X Y : C}, (X ⟶ Y) → BoundedLatticeHom (Y ⟶ obj) (X ⟶ obj)
  precomp_apply : ∀ {X Y : C} (f : X ⟶ Y) (g : Y ⟶ obj), precomp f g = f ≫ g

attribute [instance] BooleanObject.algebra

namespace BooleanObject

variable {C : Type u'} [Category.{v'} C] (B : BooleanObject C)

/-- The representing morphism for complementation. -/
def negate : B.obj ⟶ B.obj := (𝟙 B.obj)ᶜ

theorem comp_negate {X : C} (f : X ⟶ B.obj) : f ≫ B.negate = fᶜ := by
  rw [negate, ← B.precomp_apply, map_compl', B.precomp_apply, Category.comp_id]

variable [HasBinaryProducts C]

/-- The representing morphism for meet. -/
def meet : B.obj ⨯ B.obj ⟶ B.obj := prod.fst ⊓ prod.snd

/-- The representing morphism for join. -/
def join : B.obj ⨯ B.obj ⟶ B.obj := prod.fst ⊔ prod.snd

theorem lift_meet {X : C} (f g : X ⟶ B.obj) :
    prod.lift f g ≫ B.meet = f ⊓ g := by
  rw [meet, ← B.precomp_apply, map_inf, B.precomp_apply, B.precomp_apply,
    prod.lift_fst, prod.lift_snd]

theorem lift_join {X : C} (f g : X ⟶ B.obj) :
    prod.lift f g ≫ B.join = f ⊔ g := by
  rw [join, ← B.precomp_apply, map_sup, B.precomp_apply, B.precomp_apply,
    prod.lift_fst, prod.lift_snd]

variable [HasTerminal C]

omit [HasBinaryProducts C] in
theorem constant_bot (X : C) : terminal.from X ≫ (⊥ : ⊤_ C ⟶ B.obj) = ⊥ := by
  rw [← B.precomp_apply, map_bot]

omit [HasBinaryProducts C] in
theorem constant_top (X : C) : terminal.from X ≫ (⊤ : ⊤_ C ⟶ B.obj) = ⊤ := by
  rw [← B.precomp_apply, map_top]

end BooleanObject

/-- A Boolean homomorphism on all generalized elements. -/
structure BooleanMorphism {C : Type u'} [Category.{v'} C] (B B' : BooleanObject C) where
  hom : B.obj ⟶ B'.obj
  postcomp : ∀ X : C, BoundedLatticeHom (X ⟶ B.obj) (X ⟶ B'.obj)
  postcomp_apply : ∀ X (f : X ⟶ B.obj), postcomp X f = f ≫ hom

namespace BooleanMorphism

variable {C : Type u'} [Category.{v'} C] {B B' : BooleanObject C}

theorem preserves_bot (r : BooleanMorphism B B') (X : C) :
    (⊥ : X ⟶ B.obj) ≫ r.hom = ⊥ := by
  rw [← r.postcomp_apply, map_bot]

theorem preserves_top (r : BooleanMorphism B B') (X : C) :
    (⊤ : X ⟶ B.obj) ≫ r.hom = ⊤ := by
  rw [← r.postcomp_apply, map_top]

end BooleanMorphism

/-- A regular-epimorphic presentation of an internal Boolean algebra. -/
structure BooleanPresentation {C : Type u'} [Category.{v'} C] (X : C) where
  algebra : BooleanObject C
  q : X ⟶ algebra.obj
  regular : IsRegularEpi q

/-- A Boolean quotient with its regular-epimorphism proof. -/
structure BooleanQuotient {C : Type u'} [Category.{v'} C] (B : BooleanObject C) where
  target : BooleanObject C
  morphism : BooleanMorphism B target
  regular : IsRegularEpi morphism.hom

attribute [instance] BooleanPresentation.regular BooleanQuotient.regular

/-- A quotient induces another regular-epimorphic Boolean presentation. -/
def BooleanPresentation.quotient {C : Type u'} [Category.{v'} C] [Regular C]
    {X : C} (q : BooleanPresentation X) (r : BooleanQuotient q.algebra) :
    BooleanPresentation X where
  algebra := r.target
  q := q.q ≫ r.morphism.hom
  regular := inferInstance

section Fibers

variable {C : Type u'} [Category.{v'} C] [HasFiniteLimits C]

/-- The fiber over a specified global bound. -/
def boundFiber {X B : C} (q : X ⟶ B) (b : ⊤_ C ⟶ B) : Subobject X :=
  equalizerSubobject q (terminal.from X ≫ b)

/-- Preserving a bound enlarges its fiber under postcomposition. -/
theorem boundFiber_le_postcomp {X B B' : C} (q : X ⟶ B) (r : B ⟶ B')
    (b : ⊤_ C ⟶ B) (b' : ⊤_ C ⟶ B') (hb : b ≫ r = b') :
    boundFiber q b ≤ boundFiber (q ≫ r) b' := by
  have h : equalizer.ι q (terminal.from X ≫ b) ≫ (q ≫ r) =
      equalizer.ι q (terminal.from X ≫ b) ≫ (terminal.from X ≫ b') := by
    rw [← Category.assoc, equalizer.condition]
    simp only [Category.assoc, hb]
  exact Subobject.mk_le_mk_of_comm (equalizer.lift _ h) (equalizer.lift_ι _ h)

/-- The upper-bound fiber of a Boolean presentation. -/
def BooleanPresentation.positive {X : C} (q : BooleanPresentation X) : Subobject X :=
  boundFiber q.q ⊤

/-- The lower-bound fiber of a Boolean presentation. -/
def BooleanPresentation.negative {X : C} (q : BooleanPresentation X) : Subobject X :=
  boundFiber q.q ⊥

end Fibers

section Incompleteness

variable {A : Type u} [Category.{v} A] [HasBinaryProducts A]
variable {E : PredicateLattice.{v, u, w} A} {P : PredicateLattice.{v, u, w'} A}

/-- The quotient argument in the two distinct predicate lattices. -/
theorem represented_extension_incomplete (D : DiagonalData E P)
    (hU : (⊥ : E.obj D.U) ≠ ⊤)
    (represent : ∀ a : ComplementaryPair (E.obj D.U), ∃ g, D.Represents a g)
    (a b : E.obj D.S)
    (hpos : D.positive ≤ D.embedding.app D.S a)
    (hneg : D.negative ≤ D.embedding.app D.S b)
    (consistent : D.embedding.app D.S a ⊓ D.embedding.app D.S b = ⊥) :
    D.embedding.app D.S a ⊔ D.embedding.app D.S b ≠ ⊤ := by
  intro complete
  have hmeet : a ⊓ b = ⊥ := D.embedding.injective D.S (by
    rw [map_inf, map_bot]; exact consistent)
  have hjoin : a ⊔ b = ⊤ := D.embedding.injective D.S (by
    rw [map_sup, map_top]; exact complete)
  exact D.inseparable hU represent ⟨⟨a, b, IsCompl.of_eq hmeet hjoin⟩, hpos, hneg⟩

variable {C : Type u'} [Category.{v'} C] [Regular C] [FinitaryExtensive C]

/-- The incompleteness conclusion for Boolean presentations and quotients.
The input `D` is the external representation data constructed from an internal
section in `GlobalRepresentation`. -/
theorem boolean_quotient_incomplete (D : DiagonalData E P)
    (hU : (⊥ : E.obj D.U) ≠ ⊤)
    (represent : ∀ a : ComplementaryPair (E.obj D.U), ∃ g, D.Represents a g)
    {X : C} (identify : P.obj D.S ≃o Subobject X)
    (q : BooleanPresentation X)
    (hpos : identify D.positive = q.positive)
    (hneg : identify D.negative = q.negative)
    (r : BooleanQuotient q.algebra)
    (a b : E.obj D.S)
    (ha : identify (D.embedding.app D.S a) = boundFiber (q.q ≫ r.morphism.hom) ⊤)
    (hb : identify (D.embedding.app D.S b) = boundFiber (q.q ≫ r.morphism.hom) ⊥)
    (consistent : boundFiber (q.q ≫ r.morphism.hom) ⊤ ⊓
      boundFiber (q.q ≫ r.morphism.hom) ⊥ = ⊥) :
    boundFiber (q.q ≫ r.morphism.hom) ⊤ ⊔
      boundFiber (q.q ≫ r.morphism.hom) ⊥ ≠ ⊤ := by
  have hp : D.positive ≤ D.embedding.app D.S a := by
    apply identify.le_iff_le.mp
    rw [hpos, ha]
    exact boundFiber_le_postcomp q.q r.morphism.hom ⊤ ⊤ (r.morphism.preserves_top _)
  have hn : D.negative ≤ D.embedding.app D.S b := by
    apply identify.le_iff_le.mp
    rw [hneg, hb]
    exact boundFiber_le_postcomp q.q r.morphism.hom ⊥ ⊥ (r.morphism.preserves_bot _)
  have hc : D.embedding.app D.S a ⊓ D.embedding.app D.S b = ⊥ := by
    apply identify.injective
    simpa only [map_inf, map_bot, ha, hb] using consistent
  intro complete
  apply represented_extension_incomplete D hU represent a b hp hn hc
  apply identify.injective
  simpa only [map_sup, map_top, ha, hb] using complete

end Incompleteness
end CategoricalEssentialIncompleteness
