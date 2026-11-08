/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerTotalPullbackImages
import Mathlib.CategoryTheory.RegularCategory.Basic

/-! # Regularity from uniform fiber-constant descent

The returned value, rather than a selected preimage, is compiled from
the uniform graph. Surjections are not assumed to split.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Total
variable {P : Uniform.Family}

def FiberConstant {X Y Z : TotalCategory P} (e : X ⟶ Y) (h : X ⟶ Z) : Prop :=
  ∀ x x' y v v',y ∈ val e.hom x → y ∈ val e.hom x' →
    v ∈ val h.hom x → v' ∈ val h.hom x' → v=v'

def descentValue {X Y Z : TotalCategory P} (e : X ⟶ Y) (h : X ⟶ Z) (y : ℕ) : Part ℕ :=
  ⟨∃ v,∃ x,y ∈ val e.hom x ∧ v ∈ val h.hom x,fun hd => Classical.choose hd⟩

theorem mem_descentValue {X Y Z : TotalCategory P} (e : X ⟶ Y) (h : X ⟶ Z)
    (hc : FiberConstant e h) (y v : ℕ) :
    v ∈ descentValue e h y ↔ ∃ x,y ∈ val e.hom x ∧ v ∈ val h.hom x := by
  constructor
  · intro hv
    obtain ⟨hd,he⟩ := Part.mem_mk_iff.mp hv
    exact he ▸ Classical.choose_spec hd
  · rintro ⟨x,hex,hvx⟩
    let hd : ∃ v,∃ x,y ∈ val e.hom x ∧ v ∈ val h.hom x := ⟨v,x,hex,hvx⟩
    obtain ⟨x',hex',hvx'⟩ := Classical.choose_spec hd
    exact Part.mem_mk_iff.mpr ⟨hd,hc x' x y _ v hex' hex hvx' hvx⟩

theorem descentValue_represented {X Y Z : TotalCategory P} (e : X ⟶ Y) (h : X ⟶ Z)
    (hc : FiberConstant e h) : Uniform.Represented P .nat .nat (descentValue e h) := by
  have ef : Uniform.Enumerable P
      (fun a : (ℕ × ℕ) × ℕ => a.1.1 ∈ val e.hom a.2) := Uniform.Enumerable.comp
    (Computable.pair Computable.snd (Computable.fst.comp Computable.fst)) (graph_enumerable e.hom)
  have eh : Uniform.Enumerable P
      (fun a : (ℕ × ℕ) × ℕ => a.1.2 ∈ val h.hom a.2) := Uniform.Enumerable.comp
    (Computable.pair Computable.snd (Computable.snd.comp Computable.fst)) (graph_enumerable h.hom)
  apply (Uniform.represented_iff_graph_enumerable P .nat .nat _).mpr
  exact (ef.and eh).projection.of_eq (fun a => (mem_descentValue e h hc a.1 a.2).symm)

def descent {X Y Z : TotalCategory P} (e : X ⟶ Y) (he : Surjective e.hom) (h : X ⟶ Z)
    (hc : FiberConstant e h) : Y ⟶ Z :=
  let d : Y.obj ⟶ Z.obj := arrow (descentValue e h) (descentValue_represented e h hc)
    (fun y v hv => by
      obtain ⟨x,hx,_⟩ := (mem_descentValue e h hc y v).mp hv
      exact val_target e.hom x y hx)
    (fun y v hv => by
      obtain ⟨x,_,hx⟩ := (mem_descentValue e h hc y v).mp hv
      exact val_target h.hom x v hx)
  ⟨d,(total_iff d).mpr (fun y hy => by
    obtain ⟨x,hx⟩ := he y hy
    obtain ⟨v,hv⟩ := Part.dom_iff_mem.mp
      ((total_iff h.hom).mp h.property x (val_source e.hom x y hx))
    exact Part.dom_iff_mem.mpr ⟨v,(mem_descentValue e h hc y v).mpr ⟨x,hx,hv⟩⟩)⟩

theorem descent_fac {X Y Z : TotalCategory P} (e : X ⟶ Y) (he : Surjective e.hom)
    (h : X ⟶ Z) (hc : FiberConstant e h) : e ≫ descent e he h hc = h := by
  apply WideSubcategory.hom_ext
  apply val_ext_on_source
  intro x hx
  obtain ⟨y,hy⟩ := Part.dom_iff_mem.mp ((total_iff e.hom).mp e.property x hx)
  obtain ⟨v,hv⟩ := Part.dom_iff_mem.mp ((total_iff h.hom).mp h.property x hx)
  have hd : v ∈ val (descent e he h hc).hom y :=
    (mem_descentValue e h hc y v).mpr ⟨x,hy,hv⟩
  exact (Part.eq_some_iff.mpr ((mem_val_comp _ _ x v).mpr ⟨y,hy,hd⟩)).trans
    (Part.eq_some_iff.mpr hv).symm

theorem descent_unique {X Y Z : TotalCategory P} (e : X ⟶ Y) (he : Surjective e.hom)
    (h : X ⟶ Z) (hc : FiberConstant e h) (k : Y ⟶ Z) (hk : e ≫ k = h) :
    k = descent e he h hc := by
  apply WideSubcategory.hom_ext
  apply val_ext_on_source
  intro y hy
  obtain ⟨x,hx⟩ := he y hy
  obtain ⟨v,hv⟩ := Part.dom_iff_mem.mp ((total_iff k.hom).mp k.property y hy)
  have hh : v ∈ val h.hom x := by
    have ht : v ∈ val (e ≫ k).hom x := (mem_val_comp _ _ x v).mpr ⟨y,hx,hv⟩
    rwa [hk] at ht
  have hd : v ∈ val (descent e he h hc).hom y :=
    (mem_descentValue e h hc y v).mpr ⟨x,hx,hh⟩
  exact (Part.eq_some_iff.mpr hv).trans (Part.eq_some_iff.mpr hd).symm

theorem fiberConstant_of_kernelPair {X Y Z K : TotalCategory P} (e : X ⟶ Y)
    {a b : K ⟶ X} (hk : IsKernelPair e a b) (h : X ⟶ Z) (hh : a ≫ h = b ≫ h) :
    FiberConstant e h := by
  intro x x' y v v' hx hx' hv hv'
  obtain ⟨w,ha,hb⟩ := pullback_lifts_elements hk x x' y hx hx'
  have hvw : v ∈ val (a ≫ h).hom w := (mem_val_comp _ _ w v).mpr ⟨x,ha,hv⟩
  rw [hh] at hvw
  obtain ⟨u,hu,hvu⟩ := (mem_val_comp _ _ w v).mp hvw
  have he : u=x' := Part.mem_unique hu hb
  exact Part.mem_unique (he ▸ hvu) hv'

def surjectionCoforkIsColimit {X Y K : TotalCategory P} (e : X ⟶ Y)
    (he : Surjective e.hom) {a b : K ⟶ X} (hk : IsKernelPair e a b) :
    IsColimit (Cofork.ofπ e hk.w) :=
  Cofork.IsColimit.mk _
    (fun s => descent e he s.π (fiberConstant_of_kernelPair e hk s.π s.condition))
    (fun s => descent_fac e he s.π (fiberConstant_of_kernelPair e hk s.π s.condition))
    (fun s k h => descent_unique e he s.π (fiberConstant_of_kernelPair e hk s.π s.condition) k h)

def regularEpiOfSurjective {X Y : TotalCategory P} (e : X ⟶ Y) (he : Surjective e.hom) : RegularEpi e where
  W := pullback e e
  left := pullback.fst e e
  right := pullback.snd e e
  w := pullback.condition
  isColimit := surjectionCoforkIsColimit e he (IsPullback.of_hasPullback e e)

theorem isRegularEpi_of_surjective {X Y : TotalCategory P} (e : X ⟶ Y) (he : Surjective e.hom) : IsRegularEpi e :=
  ⟨⟨regularEpiOfSurjective e he⟩⟩

def imageObject {X Y : TotalCategory P} (f : X ⟶ Y) : TotalCategory P := ⟨subcarrier (Ranges.range f.hom)⟩

theorem image_supported {X Y : TotalCategory P} (f : X ⟶ Y) :
    ∀ x y,y ∈ val f.hom x → y ∈ support (Ranges.range f.hom) := by
  intro x y hy
  rw [support_range]
  exact ⟨x,hy⟩

def imageQuotient {X Y : TotalCategory P} (f : X ⟶ Y) : X ⟶ imageObject f :=
  ⟨intoSubcarrier f.hom (Ranges.range f.hom) (image_supported f),
    intoSubcarrier_total f.hom f.property _ (image_supported f)⟩

def imageInclusion {X Y : TotalCategory P} (f : X ⟶ Y) : imageObject f ⟶ Y :=
  ⟨into (Ranges.range f.hom),into_total _⟩

theorem image_factorization {X Y : TotalCategory P} (f : X ⟶ Y) : imageQuotient f ≫ imageInclusion f = f := by
  apply WideSubcategory.hom_ext
  exact intoSubcarrier_fac f.hom _ (image_supported f)

instance imageInclusion_mono {X Y : TotalCategory P} (f : X ⟶ Y) : Mono (imageInclusion f) where
  right_cancellation u v he := by
    apply WideSubcategory.hom_ext
    apply (cancel_mono (into (Ranges.range f.hom))).mp
    exact congrArg (fun k => k.hom) he

theorem imageQuotient_surjective {X Y : TotalCategory P} (f : X ⟶ Y) : Surjective (imageQuotient f).hom := by
  intro y hy
  change y ∈ support (Ranges.range f.hom) at hy
  rw [support_range] at hy
  exact hy

instance imageQuotient_regularEpi {X Y : TotalCategory P} (f : X ⟶ Y) : IsRegularEpi (imageQuotient f) :=
  isRegularEpi_of_surjective _ (imageQuotient_surjective f)

def imageFactorization {X Y : TotalCategory P} (f : X ⟶ Y) : StrongEpiMonoFactorisation f where
  I := imageObject f
  m := imageInclusion f
  e := imageQuotient f
  fac := image_factorization f

def imageIsImage {X Y : TotalCategory P} (f : X ⟶ Y) : IsImage (imageFactorization f).toMonoFactorisation :=
  (imageFactorization f).toMonoIsImage

theorem regularEpi_iff_range_top {X Y : TotalCategory P} (f : X ⟶ Y) :
    IsRegularEpi f ↔ Ranges.range f.hom = ⊤ := by
  constructor
  · intro hf
    let := hf
    let : IsIso (imageInclusion f) :=
      ExtremalEpi.isIso f (imageQuotient f) (imageInclusion f) (image_factorization f)
    apply (surjective_iff_range_top f.hom).mp
    intro y hy
    let k := inv (imageInclusion f)
    have hid : k.hom ≫ (imageInclusion f).hom = 𝟙 Y.obj :=
      congrArg (fun h => h.hom) (IsIso.inv_hom_id (imageInclusion f))
    have hm : y ∈ val (k.hom ≫ (imageInclusion f).hom) y := by
      rw [hid,val_id]
      exact (mem_supportIdentity Y.obj.support y y).mpr ⟨hy,rfl⟩
    obtain ⟨u,hu,hum⟩ := (mem_val_comp _ _ y y).mp hm
    obtain ⟨hs,he⟩ := (mem_val_idem (Ranges.range f.hom) u y).mp hum
    have hs' : y ∈ support (Ranges.range f.hom) := he ▸ hs
    rw [support_range] at hs'
    exact hs'
  · intro hf
    exact isRegularEpi_of_surjective f ((surjective_iff_range_top f.hom).mpr hf)

theorem hasCoequalizer_of_isKernelPair {X Y K : TotalCategory P} {f : X ⟶ Y} {a b : K ⟶ X}
    (h : IsKernelPair f a b) : HasCoequalizer a b := by
  rw [← image_factorization f] at h
  have hk : IsKernelPair (imageQuotient f) a b := IsKernelPair.cancel_right_of_mono h
  exact ⟨⟨_,hk.toCoequalizer'⟩⟩

instance totalRegular : Regular (TotalCategory P) where
  hasCoequalizer_of_isKernelPair := hasCoequalizer_of_isKernelPair
  regularEpiIsStableUnderBaseChange := by
    apply MorphismProperty.IsStableUnderBaseChange.of_forall_exists_isPullback
    intro X Y Z f g _ hg
    have he : Ranges.range (pullback.snd g f).hom = ⊤ := by
      rw [pullback_image (IsPullback.of_hasPullback g f),
        (regularEpi_iff_range_top g).mp hg,Idem.pull_top_of_total f.hom f.property]
    exact ⟨pullback g f,pullback.snd g f,pullback.fst g f,
      (IsPullback.of_hasPullback g f).flip,(regularEpi_iff_range_top _).mpr he⟩

end CategoricalEssentialIncompleteness.V46.Miller.Total
