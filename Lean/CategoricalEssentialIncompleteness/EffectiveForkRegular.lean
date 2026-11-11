/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.EffectiveForkPullbackImages
public import CategoricalEssentialIncompleteness.EnumerableRegular
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers

/-! # Regularity of the actual total fork category -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork

open EnumerableCarriers (Carrier val)

theorem value_in_range {X Y : Carrier} (f : X ⟶ Y) (x y : ℕ) (hy : y ∈ val f x) :
    y ∈ EnumerableCarriers.support (Ranges.range f) := by
  rw [EnumerableCarriers.support_range]
  exact ⟨x,hy⟩

def rangeFactor {X Y : Object} (f : X ⟶ Y) : X ⟶ domainObject (Ranges.range f) where
  center := EnumerableCarriers.intoSubcarrier f.center (Ranges.range f.center) (value_in_range f.center)
  left := EnumerableCarriers.intoSubcarrier f.left (Ranges.range f.left) (value_in_range f.left)
  right := EnumerableCarriers.intoSubcarrier f.right (Ranges.range f.right) (value_in_range f.right)
  natural_left := by
    intro x y u v hxy hxu hyv
    obtain ⟨_,hv⟩ := (EnumerableCarriers.mem_val_restrictMap Y.leftMap _ _
      (closed_left (Ranges.range f)) y v).mp hyv
    exact f.natural_left x y u v hxy hxu hv
  natural_right := by
    intro x y u v hxy hxu hyv
    obtain ⟨_,hv⟩ := (EnumerableCarriers.mem_val_restrictMap Y.rightMap _ _
      (closed_right (Ranges.range f)) y v).mp hyv
    exact f.natural_right x y u v hxy hxu hv

theorem rangeFactor_total {X Y : Object} (f : X ⟶ Y) (hf : isTotal f) :
    isTotal (rangeFactor f) := by
  obtain ⟨h0,h1,h2⟩ := (total_iff f).mp hf
  exact (total_iff _).mpr ⟨EnumerableCarriers.intoSubcarrier_total _ h0 _ (value_in_range f.center),
    EnumerableCarriers.intoSubcarrier_total _ h1 _ (value_in_range f.left),
    EnumerableCarriers.intoSubcarrier_total _ h2 _ (value_in_range f.right)⟩

theorem rangeFactor_inclusion {X Y : Object} (f : X ⟶ Y) :
    rangeFactor f ≫ domainInclusion (Ranges.range f)=f :=
  Hom.ext (EnumerableCarriers.intoSubcarrier_fac _ _ (value_in_range f.center))
    (EnumerableCarriers.intoSubcarrier_fac _ _ (value_in_range f.left))
    (EnumerableCarriers.intoSubcarrier_fac _ _ (value_in_range f.right))

def imageObject {X Y : Total} (f : X ⟶ Y) : Total := ⟨domainObject (Ranges.range f.hom)⟩
def imageQuotient {X Y : Total} (f : X ⟶ Y) : X ⟶ imageObject f :=
  ⟨rangeFactor f.hom,rangeFactor_total f.hom f.property⟩
def imageInclusion {X Y : Total} (f : X ⟶ Y) : imageObject f ⟶ Y :=
  ⟨domainInclusion (Ranges.range f.hom),domainInclusion_total _⟩

theorem image_factorization {X Y : Total} (f : X ⟶ Y) :
    imageQuotient f ≫ imageInclusion f=f := by
  apply WideSubcategory.hom_ext
  exact rangeFactor_inclusion f.hom

instance imageInclusion_mono {X Y : Total} (f : X ⟶ Y) : Mono (imageInclusion f) where
  right_cancellation u v he := by
    apply WideSubcategory.hom_ext
    apply Hom.ext
    · apply (cancel_mono (EnumerableCarriers.into (Ranges.range f.hom.center))).mp
      exact congrArg (fun k => k.hom.center) he
    · apply (cancel_mono (EnumerableCarriers.into (Ranges.range f.hom.left))).mp
      exact congrArg (fun k => k.hom.left) he
    · apply (cancel_mono (EnumerableCarriers.into (Ranges.range f.hom.right))).mp
      exact congrArg (fun k => k.hom.right) he

theorem imageQuotient_component_splitEpi {X Y : Total} (f : X ⟶ Y) (j : Component) :
    IsSplitEpi ((totalEvaluation j).map (imageQuotient f)) := by
  cases j
  · change IsSplitEpi (EnumerableCarriers.imageQuotient ((totalEvaluation .center).map f))
    infer_instance
  · change IsSplitEpi (EnumerableCarriers.imageQuotient ((totalEvaluation .left).map f))
    infer_instance
  · change IsSplitEpi (EnumerableCarriers.imageQuotient ((totalEvaluation .right).map f))
    infer_instance

/-- Evaluation detects the coequalizer of a kernel pair. -/
theorem regularEpi_of_components {X Y : Total} (f : X ⟶ Y)
    (hc : ∀ j : Component,IsRegularEpi ((totalEvaluation j).map f)) : IsRegularEpi f := by
  let k := IsKernelPair.of_hasPullback f
  have one (j : Component) : IsColimit ((totalEvaluation j).mapCocone (Cofork.ofπ f k.w)) := by
    letI := hc j
    refine (isColimitMapCoconeCoforkEquiv (totalEvaluation j) k.w).symm ?_
    have hk := (totalEvaluation j).map_isPullback k
    exact IsKernelPair.toCoequalizer' hk
  have hcol : IsColimit (Cofork.ofπ f k.w) := by
    letI : totalFunctor.IsEquivalence := totalEquivalence.isEquivalence_functor
    apply isColimitOfReflects totalFunctor
    apply evaluationJointlyReflectsColimits
    intro j
    rcases j with _ | (_ | _)
    · exact one .center
    · exact one .left
    · exact one .right
  exact isRegularEpi_of_regularEpi (regularEpiOfKernelPair f hcol)

instance imageQuotient_regularEpi {X Y : Total} (f : X ⟶ Y) : IsRegularEpi (imageQuotient f) := by
  apply regularEpi_of_components
  intro j
  letI := imageQuotient_component_splitEpi f j
  infer_instance

def imageFactorization {X Y : Total} (f : X ⟶ Y) : StrongEpiMonoFactorisation f where
  I := imageObject f
  m := imageInclusion f
  e := imageQuotient f
  fac := image_factorization f

def imageIsImage {X Y : Total} (f : X ⟶ Y) : IsImage (imageFactorization f).toMonoFactorisation :=
  (imageFactorization f).toMonoIsImage

theorem hasCoequalizer_of_isKernelPair {X Y K : Total} {f : X ⟶ Y} {a b : K ⟶ X}
    (h : IsKernelPair f a b) : HasCoequalizer a b := by
  rw [← image_factorization f] at h
  have hk : IsKernelPair (imageQuotient f) a b := IsKernelPair.cancel_right_of_mono h
  exact ⟨⟨_,hk.toCoequalizer'⟩⟩

theorem regularEpi_iff_range_top {X Y : Total} (f : X ⟶ Y) :
    IsRegularEpi f ↔ Ranges.range f.hom=⊤ := by
  constructor
  · intro hf
    letI := hf
    letI : IsIso (imageInclusion f) :=
      ExtremalEpi.isIso f (imageQuotient f) (imageInclusion f) (image_factorization f)
    have one (j : Component) :
        Ranges.range ((totalEvaluation j).map f).hom=⊤ := by
      letI := imageQuotient_component_splitEpi f j
      have hs : IsSplitEpi ((totalEvaluation j).map f) := by
        rw [← image_factorization f,Functor.map_comp]
        infer_instance
      letI := hs
      exact EnumerableCarriers.range_top_of_splitEpi _
    exact idem_ext (one .center) (one .left) (one .right)
  · intro hf
    apply regularEpi_of_components
    intro j
    apply (EnumerableCarriers.regularEpi_iff_range_top _).mpr
    cases j
    · exact congrArg centerIdem hf
    · exact congrArg leftIdem hf
    · exact congrArg rightIdem hf

instance totalRegular : Regular Total where
  hasCoequalizer_of_isKernelPair := hasCoequalizer_of_isKernelPair
  regularEpiIsStableUnderBaseChange := by
    apply MorphismProperty.IsStableUnderBaseChange.of_forall_exists_isPullback
    intro X Y Z f g _ hg
    have he : Ranges.range (pullback.snd g f).hom=⊤ := by
      rw [pullback_image (IsPullback.of_hasPullback g f),
        (regularEpi_iff_range_top g).mp hg,Idem.pull_top_of_total f.hom f.property]
    exact ⟨pullback g f,pullback.snd g f,pullback.fst g f,
      (IsPullback.of_hasPullback g f).flip,(regularEpi_iff_range_top _).mpr he⟩

end CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork
