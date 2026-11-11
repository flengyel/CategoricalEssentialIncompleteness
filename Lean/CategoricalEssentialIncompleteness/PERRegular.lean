/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.PERImages
public import CategoricalEssentialIncompleteness.PERPullbacks
public import Mathlib.CategoryTheory.RegularCategory.Basic

/-!
# Regularity of the numerical PER category

A regular epimorphism has an invertible image inclusion. A function representing
its inverse supplies preimages of target representatives. Applying this function
to one coordinate constructs preimages for the projection from a pullback.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CategoricalEssentialIncompleteness
namespace NumericalPER

theorem imageInclusion_isIso {R S : NumericalPER} (f : Representative R S)
    [IsRegularEpi (ofRepresentative f)] : IsIso (imageInclusion f) :=
  ExtremalEpi.isIso (ofRepresentative f) (imageQuotient f) (imageInclusion f)
    (image_factorization f)

theorem regularEpi_of_image_section {R S : NumericalPER} (f : Representative R S)
    (s : S ⟶ imagePER f) (hs : s ≫ imageInclusion f = 𝟙 S) :
    IsRegularEpi (ofRepresentative f) := by
  have hi : IsIso (imageInclusion f) := ⟨⟨s, by
    apply (cancel_mono (imageInclusion f)).mp
    simp only [Category.assoc, hs, Category.comp_id, Category.id_comp], hs⟩⟩
  exact isRegularEpi_of_regularEpi (RegularEpi.ofArrowIso
    (Arrow.isoMk (f := Arrow.mk (imageQuotient f)) (g := Arrow.mk (ofRepresentative f))
      (Iso.refl _) (asIso (imageInclusion f)) (by simp))
    (IsRegularEpi.getStruct _))

theorem image_section_output {R T : NumericalPER} (f : Representative R T)
    (h : Representative T (imagePER f))
    (hh : ofRepresentative h ≫ imageInclusion f = 𝟙 T)
    {n a b : ℕ} (hn : n ∈ T.support) (ha : a ∈ h.val n) (hb : b ∈ f.val a) :
    T.rel b n :=
  (ofRepresentative_eq_iff _ _).mp hh n hn b (Part.mem_bind ha hb) n (Part.mem_some _)

def pullbackPreimageFunction {R S T : NumericalPER} (f : Representative R T)
    (g : Representative S T) (h : Representative T (imagePER f)) :
    Representative S (product (imagePER f) S) :=
  pairRepresentative (Representative.compose g h) (Representative.identity S)

theorem pullbackPreimageFunction_snd {R S T : NumericalPER} (f : Representative R T)
    (g : Representative S T) (h : Representative T (imagePER f))
    {n a : ℕ} (ha : a ∈ (pullbackPreimageFunction f g h).val n) :
    (Nat.unpair a).2 = n := by
  obtain ⟨x, hx, y, hy, rfl⟩ := (mem_pairRepresentative _ _ _ _).mp ha
  have hy' : y = n := Part.mem_some_iff.mp hy
  simpa only [Nat.unpair_pair] using hy'

theorem pullbackPreimageFunction_supported {R S T : NumericalPER}
    (f : Representative R T) (g : Representative S T) (h : Representative T (imagePER f))
    (hh : ofRepresentative h ≫ imageInclusion f = 𝟙 T)
    {n a : ℕ} (hn : n ∈ S.support)
    (ha : a ∈ (pullbackPreimageFunction f g h).val n) :
    a ∈ (pullbackPER f g).support := by
  obtain ⟨x, hx, y, hy, rfl⟩ := (mem_pairRepresentative _ _ _ _).mp ha
  have hy' : y = n := Part.mem_some_iff.mp hy
  subst y
  obtain ⟨z, hz, hx⟩ := Part.mem_bind_iff.mp hx
  have hzT := g.output_supported hn hz
  have hxR : x ∈ R.support := (h.output_supported hzT hx).1
  have hf := Part.get_mem (f.total x hxR)
  have ha : Nat.pair x n ∈ pullbackAgreement f g := by
    exact ⟨_, by simpa using hf, z, by simpa using hz,
      image_section_output f h hh hzT hx hf⟩
  exact ⟨by simpa only [product, Nat.unpair_pair, support, Set.mem_ofPred_eq]
    using And.intro hxR hn, ha, ha⟩

/-- A partial recursive section of the image inclusion of the pullback projection. -/
def pullbackImageSectionRepresentative {R S T : NumericalPER}
    (f : Representative R T) (g : Representative S T) (h : Representative T (imagePER f))
    (hh : ofRepresentative h ≫ imageInclusion f = 𝟙 T) :
    Representative S (imagePER (pullbackSndRepresentative f g)) where
  val := (pullbackPreimageFunction f g h).val
  computable := (pullbackPreimageFunction f g h).computable
  total := (pullbackPreimageFunction f g h).total
  respects := by
    intro n m a b hnm ha hb
    refine ⟨pullbackPreimageFunction_supported f g h hh (supported_left hnm) ha,
      pullbackPreimageFunction_supported f g h hh (supported_right hnm) hb, ?_⟩
    intro x hx y hy
    have hx' : x = (Nat.unpair a).2 := Part.mem_some_iff.mp hx
    have hy' : y = (Nat.unpair b).2 := Part.mem_some_iff.mp hy
    rw [hx', hy', pullbackPreimageFunction_snd f g h ha,
      pullbackPreimageFunction_snd f g h hb]
    exact hnm

@[simp] theorem pullbackImageSection_fac {R S T : NumericalPER}
    (f : Representative R T) (g : Representative S T) (h : Representative T (imagePER f))
    (hh : ofRepresentative h ≫ imageInclusion f = 𝟙 T) :
    ofRepresentative (pullbackImageSectionRepresentative f g h hh) ≫
      imageInclusion (pullbackSndRepresentative f g) = 𝟙 S := by
  apply Quotient.sound
  intro n hn a ha b hb
  obtain ⟨x, hx, ha⟩ := Part.mem_bind_iff.mp ha
  have ha' : a = (Nat.unpair x).2 := Part.mem_some_iff.mp ha
  have hb' : b = n := Part.mem_some_iff.mp hb
  rw [ha', hb', pullbackPreimageFunction_snd f g h hx]
  exact hn

theorem pullbackSnd_regularEpi {R S T : NumericalPER}
    (f : Representative R T) (g : Representative S T)
    [IsRegularEpi (ofRepresentative f)] : IsRegularEpi (pullbackSnd f g) := by
  have := imageInclusion_isIso f
  obtain ⟨h, hh⟩ := Quotient.exists_rep (inv (imageInclusion f))
  have hs : ofRepresentative h ≫ imageInclusion f = 𝟙 T := by
    rw [show ofRepresentative h = inv (imageInclusion f) from hh]
    exact IsIso.inv_hom_id _
  exact regularEpi_of_image_section (pullbackSndRepresentative f g)
    (ofRepresentative (pullbackImageSectionRepresentative f g h hs))
    (pullbackImageSection_fac f g h hs)

instance perRegular : Regular NumericalPER where
  hasCoequalizer_of_isKernelPair := NumericalPER.hasCoequalizer_of_isKernelPair
  regularEpiIsStableUnderBaseChange := by
    apply MorphismProperty.IsStableUnderBaseChange.of_forall_exists_isPullback
    intro X Y Z f g _ hg
    revert hg
    induction f using Quotient.inductionOn with | _ f =>
      induction g using Quotient.inductionOn with | _ g =>
        intro hg
        have : IsRegularEpi (ofRepresentative g) := hg
        exact ⟨pullbackPER g f, pullbackSnd g f, pullbackFst g f,
          (pullback_isPullback g f).flip, pullbackSnd_regularEpi g f⟩

end NumericalPER
end CategoricalEssentialIncompleteness
