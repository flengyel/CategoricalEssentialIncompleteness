/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.TwoBoolean

/-!
# Complete Boolean extensions and represented decisions

This module compares Boolean quotients with Boolean homomorphisms to the constructed
internal algebra `1 + 1`. Characteristic morphisms refer to particular complementary
subobjects, not to arbitrary predicates.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u w

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness

variable {C : Type u} [Category.{v} C] [Regular C] [FinitaryExtensive C]

namespace BooleanMorphism

variable {B B' B'' : BooleanObject C}

omit [Regular C] [FinitaryExtensive C] in
@[simp]
theorem sup_comp (r : BooleanMorphism B B') {X : C} (f g : X ⟶ B.obj) :
    (f ⊔ g) ≫ r.hom = (f ≫ r.hom) ⊔ (g ≫ r.hom) := by
  rw [← r.postcomp_apply, map_sup, r.postcomp_apply, r.postcomp_apply]

omit [Regular C] [FinitaryExtensive C] in
@[simp]
theorem inf_comp (r : BooleanMorphism B B') {X : C} (f g : X ⟶ B.obj) :
    (f ⊓ g) ≫ r.hom = (f ≫ r.hom) ⊓ (g ≫ r.hom) := by
  rw [← r.postcomp_apply, map_inf, r.postcomp_apply, r.postcomp_apply]

/-- Composition of internal Boolean homomorphisms. -/
def comp (r : BooleanMorphism B B') (s : BooleanMorphism B' B'') : BooleanMorphism B B'' where
  hom := r.hom ≫ s.hom
  postcomp X := (s.postcomp X).comp (r.postcomp X)
  postcomp_apply X f := by simp [r.postcomp_apply, s.postcomp_apply]

/-- The inverse of a Boolean homomorphism whose underlying morphism is an isomorphism. -/
def inverse (r : BooleanMorphism B B') [IsIso r.hom] : BooleanMorphism B' B where
  hom := inv r.hom
  postcomp X :=
    { toFun := fun f ↦ f ≫ inv r.hom
      map_sup' := by intro f g; apply (cancel_mono r.hom).mp; simp
      map_inf' := by intro f g; apply (cancel_mono r.hom).mp; simp
      map_top' := by apply (cancel_mono r.hom).mp; simp [r.preserves_top]
      map_bot' := by apply (cancel_mono r.hom).mp; simp [r.preserves_bot] }
  postcomp_apply _ _ := rfl

/-- Preservation of bounds is the naturality equation for their copairing. -/
theorem boundCopair_comp (r : BooleanMorphism B B') :
    B.boundCopair ≫ r.hom = B'.boundCopair := by
  apply coprod.hom_ext <;>
    simp [BooleanObject.boundCopair, r.preserves_bot, r.preserves_top]

/-- Every Boolean homomorphism to `1 + 1` has the bound copairing as a section. -/
instance toTwo_isSplitEpi (r : BooleanMorphism B (twoBooleanObject (C := C))) :
    IsSplitEpi r.hom :=
  ⟨⟨⟨B.boundCopair, r.boundCopair_comp.trans twoBooleanObject_boundCopair⟩⟩⟩

end BooleanMorphism

variable {X : C} {L : Type w} [DistribLattice L] [BoundedOrder L]

/-- A represented complementary pair determines complementary subobjects. -/
def representedPartition (j : BoundedLatticeHom L (Subobject X)) (a : ComplementaryPair L) :
    SubobjectPartition X where
  positive := j a.pos
  negative := j a.neg
  complementary := IsCompl.of_eq
    (by rw [← map_inf, a.compl.inf_eq_bot, map_bot])
    (by rw [← map_sup, a.compl.sup_eq_top, map_top])

set_option backward.isDefEq.respectTransparency false in
/-- Manuscript Proposition `prop:complete-extensions-and-decisions`.
The map `j` is the embedding of restriction domains into subobjects at
the presentation object, after the manuscript's predicate identification. -/
theorem complete_extensions_and_decisions
    (j : BoundedLatticeHom L (Subobject X)) (hj : Function.Injective j)
    (q : BooleanPresentation X) :
    (∃ r : BooleanQuotient q.algebra,
      (q.quotient r).Consistent ∧ (q.quotient r).Complete ∧
        ∃ a b : L, (q.quotient r).positive = j a ∧ (q.quotient r).negative = j b) ↔
    ∃ h : BooleanMorphism q.algebra (twoBooleanObject (C := C)),
      ∃ a : ComplementaryPair L, q.q ≫ h.hom = (representedPartition j a).characteristic := by
  constructor
  · rintro ⟨r, hc, ht, a, b, ha, hb⟩
    have hm : a ⊓ b = ⊥ := hj (by
      rw [map_inf, map_bot, ← ha, ← hb]
      exact hc)
    have hs : a ⊔ b = ⊤ := hj (by
      rw [map_sup, map_top, ← ha, ← hb]
      exact ht)
    let pair : ComplementaryPair L := ⟨a, b, IsCompl.of_eq hm hs⟩
    have hi : IsIso r.target.boundCopair :=
      (q.quotient r).consistent_complete_iff_isIso.mp ⟨hc, ht⟩
    have hbi : IsIso r.target.boundMorphism.hom := hi
    let h := r.morphism.comp r.target.boundMorphism.inverse
    refine ⟨h, pair, ?_⟩
    have he : (q.q ≫ h.hom) ≫ r.target.boundCopair = (q.quotient r).q := by
      simp [h, BooleanMorphism.comp, BooleanMorphism.inverse,
        BooleanObject.boundMorphism, BooleanPresentation.quotient]
    apply (representedPartition j pair).characteristic_unique_of_fibers
    · rw [← boundFiber_mono_postcomp _ r.target.boundCopair (Two.point false), he]
      simpa only [Two.point, BooleanObject.boundCopair, coprod.inl_desc,
        BooleanPresentation.negative, representedPartition, pair] using hb
    · rw [← boundFiber_mono_postcomp _ r.target.boundCopair (Two.point true), he]
      simpa only [Two.point, BooleanObject.boundCopair, coprod.inr_desc,
        BooleanPresentation.positive, representedPartition, pair] using ha
  · rintro ⟨h, a, he⟩
    let r : BooleanQuotient q.algebra := ⟨twoBooleanObject, h, inferInstance⟩
    have hc : (q.quotient r).Consistent ∧ (q.quotient r).Complete :=
      (q.quotient r).consistent_complete_iff_isIso.mpr (by
        change IsIso (twoBooleanObject (C := C)).boundCopair
        rw [twoBooleanObject_boundCopair]
        infer_instance)
    refine ⟨r, hc.1, hc.2, a.pos, a.neg, ?_, ?_⟩
    · change boundFiber (q.q ≫ h.hom) ⊤ = j a.pos
      rw [twoBooleanObject_top, he]
      exact (representedPartition j a).characteristic_positive
    · change boundFiber (q.q ≫ h.hom) ⊥ = j a.neg
      rw [twoBooleanObject_bot, he]
      exact (representedPartition j a).characteristic_negative

section PredicateComparison

universe vA uA wE wP

variable {A : Type uA} [Category.{vA} A]
variable {E : PredicateLattice.{vA, uA, wE} A} {P : PredicateLattice.{vA, uA, wP} A}

namespace PredicateEmbedding

/-- Compose the domain-to-predicate embedding with the identification of predicates
as subobjects. The two predicate sorts remain distinct. -/
def subobjectMap (j : PredicateEmbedding E P) (S : A)
    (identify : P.obj S ≃o Subobject X) : BoundedLatticeHom (E.obj S) (Subobject X) where
  toFun := fun a ↦ identify (j.app S a)
  map_sup' := by intros; simp only [map_sup]
  map_inf' := by intros; simp only [map_inf]
  map_top' := by simp only [map_top]
  map_bot' := by simp only [map_bot]

/-- The decision equivalence with the manuscript's domain embedding and predicate comparison. -/
theorem complete_extensions_and_decisions (j : PredicateEmbedding E P) (S : A)
    (identify : P.obj S ≃o Subobject X) (q : BooleanPresentation X) :
    (∃ r : BooleanQuotient q.algebra,
      (q.quotient r).Consistent ∧ (q.quotient r).Complete ∧
        ∃ a b : E.obj S,
          (q.quotient r).positive = identify (j.app S a) ∧
          (q.quotient r).negative = identify (j.app S b)) ↔
    ∃ h : BooleanMorphism q.algebra (twoBooleanObject (C := C)),
      ∃ a : ComplementaryPair (E.obj S),
        q.q ≫ h.hom = (representedPartition (j.subobjectMap S identify) a).characteristic :=
  CategoricalEssentialIncompleteness.complete_extensions_and_decisions
    (j.subobjectMap S identify) (identify.injective.comp (j.injective S)) q

end PredicateEmbedding

variable [HasBinaryProducts A]

/-- The external diagonal obstruction excludes every represented Boolean decision.
`GlobalRepresentation` derives the representation data from the internal section. -/
theorem no_represented_boolean_decision (D : DiagonalData E P)
    (hU : (⊥ : E.obj D.U) ≠ ⊤)
    (represent : ∀ a : ComplementaryPair (E.obj D.U), ∃ g, D.Represents a g)
    (identify : P.obj D.S ≃o Subobject X) (q : BooleanPresentation X)
    (hpos : identify D.positive = q.positive)
    (hneg : identify D.negative = q.negative) :
    ¬ ∃ h : BooleanMorphism q.algebra (twoBooleanObject (C := C)),
      ∃ a : ComplementaryPair (E.obj D.S),
        q.q ≫ h.hom =
          (representedPartition (D.embedding.subobjectMap D.S identify) a).characteristic := by
  intro h
  obtain ⟨r, hc, ht, a, b, ha, hb⟩ :=
    (D.embedding.complete_extensions_and_decisions D.S identify q).mpr h
  exact boolean_quotient_incomplete D hU represent identify q hpos hneg r a b
    ha.symm hb.symm hc ht

end PredicateComparison

end CategoricalEssentialIncompleteness
