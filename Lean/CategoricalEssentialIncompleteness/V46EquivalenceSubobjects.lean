/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46FiniteLimitSubobjects
public import CategoricalEssentialIncompleteness.V46SubobjectImagePresentations

/-! # The subobject order isomorphism of a category equivalence -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.EquivalenceSubobjects
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [Regular C] [Regular D]
variable (E : C ≌ D)

omit [Regular C] [Regular D] in
theorem reflect_le {X : C} (A B : Subobject X)
    (h : FiniteLimitSubobjects.object E.functor A ≤ FiniteLimitSubobjects.object E.functor B) : A ≤ B := by
  let a := Subobject.underlyingIso (E.functor.map A.arrow)
  let b := Subobject.underlyingIso (E.functor.map B.arrow)
  let k := a.inv ≫ Subobject.ofLE _ _ h ≫ b.hom
  have hk : k ≫ E.functor.map B.arrow = E.functor.map A.arrow := by
    dsimp only [k, a, b]
    rw [Category.assoc, Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk,
      ← Category.assoc]
    erw [Category.assoc, Subobject.ofLE_arrow, Subobject.underlyingIso_arrow]
  apply Subobject.le_of_comm (E.functor.preimage k)
  apply E.functor.map_injective
  rw [E.functor.map_comp, E.functor.map_preimage]
  exact hk

omit [Regular D] in
theorem object_surjective (X : C) : Function.Surjective (FiniteLimitSubobjects.object E.functor (S := X)) := by
  intro B
  let a : E.inverse.obj (B : D) ⟶ X := E.inverse.map B.arrow ≫ (E.unitIso.app X).inv
  let : Mono a := by dsimp [a]; infer_instance
  refine ⟨Subobject.mk a, ?_⟩
  rw [FiniteLimitSubobjects.object_mk]
  let i := E.counitIso.app (B : D)
  have hu : E.functor.map (E.unitIso.app X).inv = (E.counitIso.app (E.functor.obj X)).hom := by
    apply (cancel_epi (E.functor.map (E.unitIso.app X).hom)).mp
    rw [← E.functor.map_comp, Iso.hom_inv_id, E.functor.map_id]
    exact (E.functor_unitIso_comp X).symm
  have ha : E.functor.map a = i.hom ≫ B.arrow := by
    dsimp only [a, i]
    rw [E.functor.map_comp, hu]
    exact (E.counitIso.hom.naturality B.arrow)
  have h := Subobject.mk_eq_mk_of_comm (E.functor.map a) B.arrow i ha.symm
  exact h.trans (Subobject.mk_arrow B)

def orderIso (X : C) : Subobject X ≃o Subobject (E.functor.obj X) :=
  {
    toEquiv := Equiv.ofBijective (FiniteLimitSubobjects.object E.functor) ⟨
      (by intro A B h; exact le_antisymm (reflect_le E A B h.le) (reflect_le E B A h.ge)),
      object_surjective E X⟩
    map_rel_iff' := by
      intro A B
      exact ⟨reflect_le E A B, fun h => FiniteLimitSubobjects.object_monotone E.functor h⟩ }

omit [Regular D] in
theorem orderIso_apply {X : C} (A : Subobject X) :
    orderIso E X A = FiniteLimitSubobjects.object E.functor A := rfl

theorem object_image {X Y : C} (f : X ⟶ Y) :
    FiniteLimitSubobjects.object E.functor (imageSubobject f) = imageSubobject (E.functor.map f) := by
  rw [FiniteLimitSubobjects.object_mk]
  let F : StrongEpiMonoFactorisation (E.functor.map f) :=
    { I := E.functor.obj (image f)
      e := E.functor.map (factorThruImage f)
      m := E.functor.map (image.ι f)
      fac := by rw [← E.functor.map_comp, image.fac] }
  exact (SubobjectPredicates.image_of_factorization F).symm

theorem object_exists {X Y : C} (f : X ⟶ Y) (A : Subobject X) :
    FiniteLimitSubobjects.object E.functor ((Subobject.«exists» f).obj A) =
      (Subobject.«exists» (E.functor.map f)).obj (FiniteLimitSubobjects.object E.functor A) := by
  rw [SubobjectImagePresentations.exists_eq_image, object_image, E.functor.map_comp]
  change imageSubobject (E.functor.map A.arrow ≫ E.functor.map f) =
    (Subobject.«exists» (E.functor.map f)).obj (Subobject.mk (E.functor.map A.arrow))
  exact (SubobjectImagePresentations.exists_mk (E.functor.map A.arrow) (E.functor.map f)).symm

variable [FinitaryExtensive C] [FinitaryExtensive D]

/-- Both inseparability and the quantifier over complementary separators
are invariant under the equivalence. -/
theorem inseparable {X : C} {a b : Subobject X} (h : SubobjectInseparable a b) :
    SubobjectInseparable (FiniteLimitSubobjects.object E.functor a) (FiniteLimitSubobjects.object E.functor b) := by
  let e := orderIso E X
  constructor
  · change e a ⊓ e b = ⊥
    rw [← e.map_inf, h.1, e.map_bot]
  · rintro ⟨p, ha, hb⟩
    change e a ≤ p.positive at ha
    change e b ≤ p.negative at hb
    apply h.2
    have hp : IsCompl (e.symm p.positive) (e.symm p.negative) := by
      constructor
      · apply disjoint_iff.mpr
        rw [← e.symm.map_inf, p.complementary.inf_eq_bot, e.symm.map_bot]
      · apply codisjoint_iff.mpr
        rw [← e.symm.map_sup, p.complementary.sup_eq_top, e.symm.map_top]
    refine ⟨⟨e.symm p.positive, e.symm p.negative, hp⟩, ?_, ?_⟩
    · simpa only [e.symm_apply_apply] using e.symm.monotone ha
    · simpa only [e.symm_apply_apply] using e.symm.monotone hb

end CategoricalEssentialIncompleteness.V46.EquivalenceSubobjects
