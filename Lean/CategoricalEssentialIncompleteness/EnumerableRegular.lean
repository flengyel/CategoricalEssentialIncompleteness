/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.EnumerablePullbackImages
import CategoricalEssentialIncompleteness.EnumerableChoice
import Mathlib.CategoryTheory.RegularCategory.Basic

/-! # Regularity of the category of total recursive c.e. carrier maps -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableCarriers

def imageObject {X Y : Total} (f : X ⟶ Y) : Total := ⟨subcarrier (Ranges.range f.hom)⟩

theorem image_supported {X Y : Total} (f : X ⟶ Y) :
    ∀ x y,y ∈ val f.hom x → y ∈ support (Ranges.range f.hom) := by
  intro x y hy
  rw [support_range]
  exact ⟨x,hy⟩

def imageQuotient {X Y : Total} (f : X ⟶ Y) : X ⟶ imageObject f :=
  ⟨intoSubcarrier f.hom (Ranges.range f.hom) (image_supported f),
    intoSubcarrier_total f.hom f.property (Ranges.range f.hom) (image_supported f)⟩

def imageInclusion {X Y : Total} (f : X ⟶ Y) : imageObject f ⟶ Y :=
  ⟨into (Ranges.range f.hom),into_total _⟩

theorem image_factorization {X Y : Total} (f : X ⟶ Y) :
    imageQuotient f ≫ imageInclusion f=f := by
  apply WideSubcategory.hom_ext
  exact intoSubcarrier_fac f.hom _ (image_supported f)

instance imageInclusion_mono {X Y : Total} (f : X ⟶ Y) : Mono (imageInclusion f) where
  right_cancellation u v he := by
    apply WideSubcategory.hom_ext
    apply (cancel_mono (into (Ranges.range f.hom))).mp
    exact congrArg (fun k => k.hom) he

theorem imageQuotient_surjective {X Y : Total} (f : X ⟶ Y) :
    Surjective (imageQuotient f).hom := by
  intro y hy
  change y ∈ support (Ranges.range f.hom) at hy
  rw [support_range] at hy
  exact hy

theorem isSplitEpi_of_surjective {X Y : Total} (f : X ⟶ Y) (hf : Surjective f.hom) :
    IsSplitEpi f := by
  obtain ⟨s,hs,he⟩ := surjective_section f.hom hf
  apply IsSplitEpi.mk'
  refine ⟨⟨s,hs⟩,?_⟩
  apply WideSubcategory.hom_ext
  exact he

instance imageQuotient_splitEpi {X Y : Total} (f : X ⟶ Y) : IsSplitEpi (imageQuotient f) :=
  isSplitEpi_of_surjective _ (imageQuotient_surjective f)

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

theorem range_top_of_splitEpi {X Y : Total} (f : X ⟶ Y) [IsSplitEpi f] :
    Ranges.range f.hom=⊤ := by
  apply (surjective_iff_range_top f.hom).mp
  intro y hy
  have he : (section_ f).hom ≫ f.hom=𝟙 Y.obj := congrArg (fun k => k.hom) (IsSplitEpi.id f)
  have hm : y ∈ val ((section_ f).hom ≫ f.hom) y := by
    rw [he,val_id]
    exact (mem_supportIdentity Y.obj.support y y).mpr ⟨hy,rfl⟩
  exact (mem_val_comp _ _ y y).mp hm |>.imp (fun _ h => h.2)

theorem regularEpi_iff_range_top {X Y : Total} (f : X ⟶ Y) :
    IsRegularEpi f ↔ Ranges.range f.hom=⊤ := by
  constructor
  · intro hf
    letI := hf
    letI : IsIso (imageInclusion f) :=
      ExtremalEpi.isIso f (imageQuotient f) (imageInclusion f) (image_factorization f)
    have hs : IsSplitEpi f := by
      rw [← image_factorization f]
      infer_instance
    letI := hs
    exact range_top_of_splitEpi f
  · intro hf
    letI := isSplitEpi_of_surjective f ((surjective_iff_range_top f.hom).mpr hf)
    infer_instance

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

end CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableCarriers
