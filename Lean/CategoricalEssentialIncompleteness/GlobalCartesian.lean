/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.InternalCartesian

/-!
# Global arrows and predicates

Global points of the internal total hom-objects form an ordinary category.
Its binary products are induced by the internal product operations. The
comparison with Mathlib's chosen products is an isomorphism, with explicit
projection equations. Global predicates and the monic internal embedding
give the external predicate lattice and its natural injective embedding.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe v u w
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness

namespace InternalHom
variable {V : Type u} [Category.{v} V] [HasFiniteLimits V] {O : Type w}
variable (H : InternalHom V O)

/-- Objects of the ordinary category of global arrows. -/
structure Global (H : InternalHom V O) where
  obj : O

variable [H.CartesianLaws]

instance globalCategory : Category H.Global where
  Hom X Y := ⊤_ V ⟶ H.hom X.obj Y.obj
  id X := H.identity X.obj
  comp f g := H.comp f g
  id_comp := CartesianLaws.id_comp
  comp_id := CartesianLaws.comp_id
  assoc := CartesianLaws.assoc

def globalProduct (X Y : H.Global) : H.Global := ⟨H.product X.obj Y.obj⟩
def globalFst (X Y : H.Global) : H.globalProduct X Y ⟶ X := H.fst X.obj Y.obj
def globalSnd (X Y : H.Global) : H.globalProduct X Y ⟶ Y := H.snd X.obj Y.obj
def globalPair {A X Y : H.Global} (f : A ⟶ X) (g : A ⟶ Y) :
    A ⟶ H.globalProduct X Y := H.pair f g

@[simp] theorem globalPair_fst {A X Y : H.Global} (f : A ⟶ X) (g : A ⟶ Y) :
    H.globalPair f g ≫ H.globalFst X Y = f := CartesianLaws.pair_fst f g
@[simp] theorem globalPair_snd {A X Y : H.Global} (f : A ⟶ X) (g : A ⟶ Y) :
    H.globalPair f g ≫ H.globalSnd X Y = g := CartesianLaws.pair_snd f g

def globalBinaryFan (X Y : H.Global) : BinaryFan X Y :=
  BinaryFan.mk (H.globalFst X Y) (H.globalSnd X Y)

/-- The internal product operations give the ordinary product universal property. -/
def globalBinaryFanIsLimit (X Y : H.Global) : IsLimit (H.globalBinaryFan X Y) :=
  BinaryFan.isLimitMk
    (fun t ↦ H.globalPair t.fst t.snd)
    (fun t ↦ H.globalPair_fst t.fst t.snd)
    (fun t ↦ H.globalPair_snd t.fst t.snd)
    (fun _ m hf hg ↦ by
      change m = H.pair _ _
      rw [← CartesianLaws.pair_eta m]
      exact congrArg₂ H.pair hf hg)

instance globalHasBinaryProduct (X Y : H.Global) : HasLimit (Limits.pair X Y) :=
  ⟨⟨_, H.globalBinaryFanIsLimit X Y⟩⟩

instance globalHasBinaryProducts : HasBinaryProducts H.Global :=
  hasBinaryProducts_of_hasLimit_pair H.Global

/-- The chosen categorical product compared with the enriched product object. -/
def globalProductIso (X Y : H.Global) : X ⨯ Y ≅ H.globalProduct X Y :=
  limit.isoLimitCone ⟨H.globalBinaryFan X Y, H.globalBinaryFanIsLimit X Y⟩

@[simp, reassoc] theorem globalProductIso_hom_fst (X Y : H.Global) :
    (H.globalProductIso X Y).hom ≫ H.globalFst X Y = prod.fst :=
  limit.isoLimitCone_hom_π
    ⟨H.globalBinaryFan X Y, H.globalBinaryFanIsLimit X Y⟩ ⟨WalkingPair.left⟩

@[simp, reassoc] theorem globalProductIso_hom_snd (X Y : H.Global) :
    (H.globalProductIso X Y).hom ≫ H.globalSnd X Y = prod.snd :=
  limit.isoLimitCone_hom_π
    ⟨H.globalBinaryFan X Y, H.globalBinaryFanIsLimit X Y⟩ ⟨WalkingPair.right⟩

@[simp] theorem lift_globalProductIso {A X Y : H.Global} (f : A ⟶ X) (g : A ⟶ Y) :
    prod.lift f g ≫ (H.globalProductIso X Y).hom = H.globalPair f g := by
  apply H.hom_ext <;>
    first
    | change (prod.lift f g ≫ (H.globalProductIso X Y).hom) ≫ H.globalFst X Y =
        H.globalPair f g ≫ H.globalFst X Y
      simp only [Category.assoc, H.globalProductIso_hom_fst, prod.lift_fst,
        H.globalPair_fst]
    | change (prod.lift f g ≫ (H.globalProductIso X Y).hom) ≫ H.globalSnd X Y =
        H.globalPair f g ≫ H.globalSnd X Y
      simp only [Category.assoc, H.globalProductIso_hom_snd, prod.lift_snd,
        H.globalPair_snd]

/-- The product comparison respects the two-arrow product operation. -/
theorem globalProductIso_naturality {X Y X' Y' : H.Global}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    prod.map f g ≫ (H.globalProductIso X' Y').hom =
      (H.globalProductIso X Y).hom ≫
        H.globalPair (H.globalFst X Y ≫ f) (H.globalSnd X Y ≫ g) := by
  apply H.hom_ext
  · change (prod.map f g ≫ (H.globalProductIso X' Y').hom) ≫ H.globalFst X' Y' =
      ((H.globalProductIso X Y).hom ≫
        H.globalPair (H.globalFst X Y ≫ f) (H.globalSnd X Y ≫ g)) ≫ H.globalFst X' Y'
    simp [Category.assoc, H.globalProductIso_hom_fst_assoc]
  · change (prod.map f g ≫ (H.globalProductIso X' Y').hom) ≫ H.globalSnd X' Y' =
      ((H.globalProductIso X Y).hom ≫
        H.globalPair (H.globalFst X Y ≫ f) (H.globalSnd X Y ≫ g)) ≫ H.globalSnd X' Y'
    simp [Category.assoc, H.globalProductIso_hom_snd_assoc]

end InternalHom

namespace InternalPredicates
variable {V : Type u} [Category.{v} V] [HasFiniteLimits V] {O : Type w}
variable {H : InternalHom V O} [H.CartesianLaws] (P : InternalPredicates H)

/-- The contravariant bounded lattice of global predicates. -/
def globalPredicates : PredicateLattice H.Global where
  obj X := ⊤_ V ⟶ (P.lattice X.obj).obj
  lattice X := (P.lattice X.obj).lattice _
  bounds X := (P.lattice X.obj).bounds _
  pull := P.pull
  pull_id _ := P.pull_id
  pull_comp := P.pull_comp

end InternalPredicates

namespace InternalPredicateEmbedding
variable {V : Type u} [Category.{v} V] [HasFiniteLimits V] {O : Type w}
variable {H : InternalHom V O} [H.CartesianLaws] {E P : InternalPredicates H}

/-- The global natural embedding is induced by the internal monic components. -/
def globalEmbedding (j : InternalPredicateEmbedding E P) :
    PredicateEmbedding E.globalPredicates P.globalPredicates where
  app X := (j.app X.obj).postcomp _
  injective X := j.injective _ X.obj
  naturality f e := by
    simpa only [InternalPredicates.globalPredicates, InternalLatticeHom.postcomp_apply]
      using j.naturality f e

end InternalPredicateEmbedding
end CategoricalEssentialIncompleteness
