/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PartialSliceAdjunctions
public import CategoricalEssentialIncompleteness.V46PartialMapFunctorComposition

/-! # Composition and the literal partial unit on monic spans -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.PartialSliceChangeBase

open RestrictionSubobjects
variable {C : Type u} [Category.{v} C] [PCategoryStruct C] [PCategory C] [Splits C]
variable [HasPullbacks (Tot C)] {T U V : Tot C} (i : T ⟶ U)
attribute [local instance] overMapMonos overMapPullbacks

omit [Splits C] in
theorem postcompose_comp (j : U ⟶ V) : postcompose i ⋙ postcompose j = postcompose (i ≫ j) := by
  exact (PartialMaps.inducedFunctor_comp (Over.map i) (Over.map j)).symm.trans
    (PartialMaps.inducedFunctor_congr _ _ (Over.mapComp_eq i j).symm)

omit i [Splits C] in
theorem postcompose_id (P : Tot C) : postcompose (𝟙 P) = 𝟭 (PartialMaps.Par (Over P)) := by
  exact (PartialMaps.inducedFunctor_congr _ _ (Over.mapId_eq P)).trans
    PartialMaps.inducedFunctor_id

variable (inverses : MonoInverses C)

def pullbackInclusion (Y : PartialMaps.Par (Over U)) :
    ((postcompose i).obj ((reindex i inverses).obj Y)).obj ⟶ Y.obj :=
  Over.homMk (pullback.fst Y.obj.hom i) (pullback.condition (f := Y.obj.hom) (g := i))

variable [Mono i]

instance pullbackInclusion_mono (Y : PartialMaps.Par (Over U)) :
    Mono (pullbackInclusion i inverses Y) := by
  have : Mono (pullbackInclusion i inverses Y).left := by
    change Mono (pullback.fst Y.obj.hom i)
    infer_instance
  exact Over.mono_of_mono_left _

/-- The second unit is the literal partial identity whose domain is the pullback
monomorphism, in the monic-span quotient. -/
theorem right_unit_span (Y : PartialMaps.Par (Over U)) :
    (rightAdjunction i inverses).unit.app Y =
      PartialMaps.inverseMono (pullbackInclusion i inverses Y) := by
  apply (PartialSliceEquivalence.functor inverses U).map_injective
  rw [right_unit_value]
  apply AmbientPartialSlice.Hom.ext
  change inverse inverses (pullback.fst Y.obj.hom i) =
    inverse inverses (pullback.fst Y.obj.hom i) ≫ 𝟙 _
  exact (Category.comp_id _).symm

/-- For a proper inclusion, the second unit at the terminal family is
partial: totality would make that family isomorphic to an image object. -/
theorem right_unit_not_total (proper : ¬ IsIso i) :
    ¬ isTotal ((rightAdjunction i inverses).unit.app
      (⟨Over.mk (𝟙 U)⟩ : PartialMaps.Par (Over U))) := by
  intro ht
  let Z : PartialMaps.Par (Over U) := ⟨Over.mk (𝟙 U)⟩
  have ht' : rst (PartialMaps.inverseMono (pullbackInclusion i inverses Z)) = 𝟙 Z := by
    change rst ((rightAdjunction i inverses).unit.app Z) = 𝟙 Z at ht
    rwa [right_unit_span] at ht
  let e : (postcompose i).obj ((reindex i inverses).obj Z) ≅ Z :=
    { hom := PartialMaps.ofTotal (pullbackInclusion i inverses Z)
      inv := PartialMaps.inverseMono (pullbackInclusion i inverses Z)
      hom_inv_id := PartialMaps.total_inverseMono _
      inv_hom_id := (PartialMaps.inverseMono_total _).trans ht' }
  exact proper (PartialSliceProperness.isIso_of_terminal_image i
    ((PartialSliceEquivalence.functor inverses T).obj ((reindex i inverses).obj Z))
    ((PartialSliceEquivalence.functor inverses U).mapIso e))

end CategoricalEssentialIncompleteness.V46.PartialSliceChangeBase
