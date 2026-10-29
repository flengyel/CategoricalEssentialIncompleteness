/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.BooleanPresentations

/-!
# The predicate lattice of subobjects

In a regular finitely extensive category, images commute with pullback and
pullback preserves finite joins. Consequently, subobjects form bounded
distributive lattices, with bounded lattice homomorphisms as reindexing maps.
-/

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness
namespace SubobjectPredicates

variable {C : Type u} [Category.{v} C]

/-- A strong epimorphism followed by a monomorphism presents the image. -/
theorem image_of_factorization [HasImages C] {X Y : C} {f : X ⟶ Y}
    (F : StrongEpiMonoFactorisation f) : imageSubobject f = Subobject.mk F.m := by
  exact Subobject.mk_eq_mk_of_comm _ _
    (IsImage.isoExt (Image.isImage f) F.toMonoIsImage) (IsImage.isoExt_hom_m _ _)

/-- In a regular category, the image of a pullback is the pullback of the image. -/
theorem image_pullback [Regular C] {P X A Y : C}
    {p : P ⟶ X} {q : P ⟶ A} {f : X ⟶ Y} {g : A ⟶ Y}
    (h : IsPullback p q f g) :
    imageSubobject p = (Subobject.pullback f).obj (imageSubobject g) := by
  let k : P ⟶ pullback (image.ι g) f :=
    pullback.lift (q ≫ factorThruImage g) p (by simp [Category.assoc, h.w])
  have hk : IsPullback k q (pullback.fst (image.ι g) f) (factorThruImage g) := by
    apply IsPullback.of_right (h₁₂ := pullback.snd (image.ι g) f)
      (h₂₂ := image.ι g)
    · simpa [k] using h
    · simp [k]
    · exact (IsPullback.of_hasPullback (image.ι g) f).flip
  have : IsRegularEpi k :=
    Regular.regularEpiIsStableUnderBaseChange.of_isPullback hk.flip
      (inferInstance : IsRegularEpi (factorThruImage g))
  let F : StrongEpiMonoFactorisation p :=
    { I := pullback (image.ι g) f
      e := k
      m := pullback.snd (image.ι g) f
      fac := by simp [k] }
  rw [image_of_factorization F]
  exact (Subobject.pullback_obj_mk (IsPullback.of_hasPullback (image.ι g) f)).symm

/-- Pullback preserves binary joins of subobjects in a regular finitely extensive category. -/
theorem pullback_sup [Regular C] [FinitaryExtensive C]
    {X Y : C} (f : X ⟶ Y) (A B : Subobject Y) :
    (Subobject.pullback f).obj (A ⊔ B) =
      (Subobject.pullback f).obj A ⊔ (Subobject.pullback f).obj B := by
  have h := PresentationLemmas.copair_isPullback A.arrow B.arrow f
    ((Subobject.pullback f).obj A).arrow (Subobject.pullbackπ f A)
    ((Subobject.pullback f).obj B).arrow (Subobject.pullbackπ f B)
    (Subobject.isPullback f A).flip (Subobject.isPullback f B).flip
    (coprodIsCoprod _ _)
  simpa only [PresentationLemmas.desc_coprod, PresentationLemmas.image_copair,
    imageSubobject_mono, Subobject.mk_arrow] using (image_pullback h).symm

/-- Direct image along a monomorphism preserves binary joins. -/
theorem map_sup [HasPullbacks C] [HasImages C] [HasBinaryCoproducts C]
    {X Y : C} (f : X ⟶ Y) [Mono f] (A B : Subobject X) :
    (Subobject.map f).obj (A ⊔ B) =
      (Subobject.map f).obj A ⊔ (Subobject.map f).obj B := by
  have h : GaloisConnection (Subobject.map f).obj (Subobject.pullback f).obj := by
    intro A B
    exact ⟨fun h => ((Subobject.mapPullbackAdj f).homEquiv A B h.hom).le,
      fun h => (((Subobject.mapPullbackAdj f).homEquiv A B).symm h.hom).le⟩
  exact h.l_sup

/-- Intersection distributes over binary joins of subobjects. -/
theorem inf_sup [Regular C] [FinitaryExtensive C] {X : C} (A B D : Subobject X) :
    A ⊓ (B ⊔ D) = A ⊓ B ⊔ A ⊓ D := by
  simp only [Subobject.inf_eq_map_pullback, pullback_sup, map_sup]

/-- Subobjects of an object in a regular finitely extensive category form a distributive lattice. -/
instance subobjectDistribLattice [Regular C] [FinitaryExtensive C] (X : C) :
    DistribLattice (Subobject X) :=
  DistribLattice.ofInfSupLe fun A B D => (inf_sup A B D).le

/-- Pullback of subobjects as a bounded lattice homomorphism. -/
def pullbackHom [Regular C] [FinitaryExtensive C] {X Y : C} (f : X ⟶ Y) :
    BoundedLatticeHom (Subobject Y) (Subobject X) where
  toFun := (Subobject.pullback f).obj
  map_inf' := Subobject.inf_pullback f
  map_sup' := pullback_sup f
  map_top' := Subobject.pullback_top f
  map_bot' := PresentationLemmas.pullback_bot f

end SubobjectPredicates

/-- The bounded distributive predicate lattices of subobjects, reindexed by pullback. -/
def subobjectPredicates (C : Type u) [Category.{v} C] [Regular C] [FinitaryExtensive C] :
    PredicateLattice C where
  obj X := Subobject X
  lattice _ := inferInstance
  bounds _ := inferInstance
  pull f := SubobjectPredicates.pullbackHom f
  pull_id _ := Subobject.pullback_id
  pull_comp f g := Subobject.pullback_comp f g

end CategoricalEssentialIncompleteness
