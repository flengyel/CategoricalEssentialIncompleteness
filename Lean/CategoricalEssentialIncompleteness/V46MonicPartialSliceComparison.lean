/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46PartialMapFunctor
public import CategoricalEssentialIncompleteness.V46PartialMapTotals
public import CategoricalEssentialIncompleteness.V46PartialSliceChangeBase

/-! # Postcomposition of partial maps in ordinary slices over a monomorphism -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.MonicPartialSliceComparison
open PartialMaps
variable {D : Type u} [Category.{v} D] [HasPullbacks D]

/-- The total value of a total monomorphism is monic under the total equivalence. -/
theorem inverses : RestrictionSubobjects.MonoInverses (Par D) := by
  intro X Y m hm
  let v := totalValue m.hom m.property
  have he : toTotal.map v = m := WideSubcategory.hom_ext _ (ofTotal_totalValue _ _)
  have : Mono (toTotal.map v) := he ▸ hm
  have : Mono v := (toTotal (D := D)).mono_of_mono_map inferInstance
  refine ⟨inverseMono (X := X.obj) (Y := Y.obj) v, ?_, ?_⟩
  · rw [← ofTotal_totalValue m.hom m.property]
    exact total_inverseMono v
  · rw [← ofTotal_totalValue m.hom m.property]
    exact inverseMono_total v

variable {T U : D} (i : T ⟶ U)
local instance : (Over.map i).PreservesMonomorphisms where
  preserves f _ := by
    have : Mono f.left := Over.mono_left_of_mono f
    have : Mono ((Over.map i).map f).left := this
    exact Over.mono_of_mono_left _
local instance : PreservesLimitsOfShape WalkingCospan (Over.map i) := by
  let : PreservesLimitsOfShape WalkingCospan (Over.map i ⋙ Over.forget U) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan (Over.forget T))
  exact preservesLimitsOfShape_of_reflects_of_preserves (Over.map i) (Over.forget U)

def postcompose : Par (Over T) ⥤ Par (Over U) := inducedFunctor (Over.map i)

theorem postcompose_total {X Y : Par (Over T)} (f : X.obj ⟶ Y.obj) :
    (postcompose i).map (ofTotal (X := X) (Y := Y) f) = ofTotal ((Over.map i).map f) :=
  inducedFunctor_ofTotal (Over.map i) f

theorem preserves_restriction : PreservesRestriction (postcompose i) :=
  inducedFunctor_restriction (Over.map i)

theorem faithful : (postcompose i).Faithful where
  map_injective {X Y} f g h := by
    induction f using Quotient.inductionOn with | _ s =>
      induction g using Quotient.inductionOn with | _ t =>
        obtain ⟨e⟩ := (ofSpan_eq_iff (rawMap (Over.map i) s) (rawMap (Over.map i) t)).mp h
        let z := CategoryTheory.Span.SpanBicat.apexIso e
        have hl : z.hom.left ≫ t.l.left = s.l.left := congrArg (fun m => m.left) e.hom.hom_l
        have hr : z.hom.left ≫ t.r.left = s.r.left := congrArg (fun m => m.left) e.hom.hom_r
        have hw : z.hom.left ≫ t.apex.hom = s.apex.hom := by
          rw [← Over.w t.l, ← Category.assoc, hl, Over.w s.l]
        apply ofSpan_eq_of_iso
        exact CategoryTheory.Span.mkIso (Over.isoMk ((Over.forget U).mapIso z) hw)
          (Over.OverMorphism.ext hl) (Over.OverMorphism.ext hr)

variable [Mono i]

/-- Lift a span by using its left leg to place its apex over T.
Monicity of i makes the right leg a morphism over T as well. -/
def liftSpan {X Y : Par (Over T)} (s : Raw ((postcompose i).obj X) ((postcompose i).obj Y)) :
    Raw X Y := by
  let A := Over.mk (s.l.left ≫ X.obj.hom)
  let l : A ⟶ X.obj := Over.homMk s.l.left rfl
  have hw : s.r.left ≫ Y.obj.hom = s.l.left ≫ X.obj.hom := by
    apply (cancel_mono i).mp
    rw [Category.assoc, Category.assoc]
    exact (Over.w s.r).trans (Over.w s.l).symm
  let r : A ⟶ Y.obj := Over.homMk s.r.left hw
  have : Mono s.l.left := Over.mono_left_of_mono s.l
  have : Mono l := Over.mono_of_mono_left l
  exact ⟨A, l, r, inferInstance, trivial⟩

theorem full : (postcompose i).Full where
  map_surjective {X Y} f := by
    induction f using Quotient.inductionOn with | _ s =>
      refine ⟨ofSpan (liftSpan i s), ofSpan_eq_of_iso ?_⟩
      let z : (rawMap (Over.map i) (liftSpan i s)).apex ≅ s.apex :=
        Over.isoMk (Iso.refl s.apex.left) (by
          change 𝟙 _ ≫ s.apex.hom = (s.l.left ≫ X.obj.hom) ≫ i
          rw [Category.id_comp, Category.assoc]
          exact (Over.w s.l).symm)
      exact CategoryTheory.Span.mkIso z
        (Over.OverMorphism.ext (Category.id_comp s.l.left))
        (Over.OverMorphism.ext (Category.id_comp s.r.left))

theorem proper (h : ¬ IsIso i) : ¬ (postcompose i).EssSurj := by
  intro surj
  let := surj
  let Z : Par (Over U) := ⟨Over.mk (𝟙 U)⟩
  let X := (postcompose i).objPreimage Z
  let e := (postcompose i).objObjPreimageIso Z
  let k := totalValue e.inv (iso_total e.symm)
  have hk : (k.left ≫ X.obj.hom) ≫ i = 𝟙 U := by
    rw [Category.assoc]
    exact Over.w k
  apply h
  exact ⟨⟨k.left ≫ X.obj.hom, (cancel_mono i).mp (by simp [Category.assoc, hk]), hk⟩⟩

end CategoricalEssentialIncompleteness.V46.MonicPartialSliceComparison
