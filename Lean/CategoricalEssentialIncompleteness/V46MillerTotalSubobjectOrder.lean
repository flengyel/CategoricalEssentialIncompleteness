/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerTotalPartialMaps
public import Mathlib.CategoryTheory.Subobject.Limits

/-! # Subobject order from actual numerical images

A factor through a monomorphism uses its proved partial inverse. It does
not choose a preimage in a general surjection or a proof from each nonempty
proof fiber. This comparison applies to arbitrary uniformly semidecidable
carriers, including the actual sentence carrier.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Total.Subobjects
variable {P : Uniform.Family}

def imageCodes {X Y : TotalCategory P} (f : X ⟶ Y) : Set ℕ :=
  {y | ∃ x, y ∈ val f.hom x}

/-- The existing categorical partial inverse of a mono has its exact
reversed graph. Its uniqueness makes this graph representation independent. -/
theorem inverse_graph {X Y : TotalCategory P} (m : X ⟶ Y) [Mono m] (y x : ℕ) :
    x ∈ val (PartialSpans.inverse m) y ↔ y ∈ val m.hom x := by
  constructor
  · intro hx
    have hxS := val_target (PartialSpans.inverse m) y x hx
    obtain ⟨z,hz⟩ := Part.dom_iff_mem.mp ((total_iff m.hom).mp m.property x hxS)
    have hc : z ∈ val (PartialSpans.inverse m ≫ m.hom) y :=
      (mem_val_comp _ _ y z).mpr ⟨x,hx,hz⟩
    rw [PartialSpans.inverse_hom] at hc
    have he : z=y := ((mem_val_restriction (PartialSpans.inverse m) y z).mp hc).2
    exact he ▸ hz
  · intro hy
    have hid : x ∈ val (𝟙 X.obj) x :=
      (mem_supportIdentity X.obj.support x x).mpr ⟨val_source m.hom x y hy,rfl⟩
    rw [← PartialSpans.hom_inverse m] at hid
    obtain ⟨z,hz,hx⟩ := (mem_val_comp _ _ x x).mp hid
    have he : z=y := Part.mem_unique hz hy
    exact he ▸ hx

/-- This actual composition is total precisely because each output of f
lies in the mono's image. Only the unique inverse of that mono is searched. -/
def factorThroughMono {X Y Z : TotalCategory P} (f : X ⟶ Z) (m : Y ⟶ Z) [Mono m]
    (h : imageCodes f ⊆ imageCodes m) : X ⟶ Y :=
  ⟨f.hom ≫ PartialSpans.inverse m,(total_iff _).mpr (by
    intro x hx
    obtain ⟨y,hy⟩ := Part.dom_iff_mem.mp ((total_iff f.hom).mp f.property x hx)
    obtain ⟨z,hz⟩ := h ⟨x,hy⟩
    exact Part.dom_iff_mem.mpr ⟨z,(mem_val_comp _ _ x z).mpr
      ⟨y,hy,(inverse_graph m y z).mpr hz⟩⟩)⟩

theorem factorThroughMono_graph {X Y Z : TotalCategory P} (f : X ⟶ Z) (m : Y ⟶ Z) [Mono m]
    (h : imageCodes f ⊆ imageCodes m) (x z : ℕ) :
    z ∈ val (factorThroughMono f m h).hom x ↔
      ∃ y,y ∈ val f.hom x ∧ y ∈ val m.hom z := by
  change z ∈ val (f.hom ≫ PartialSpans.inverse m) x ↔ _
  rw [mem_val_comp]
  exact exists_congr (fun y => and_congr_right (fun _ => inverse_graph m y z))

theorem factorThroughMono_fac {X Y Z : TotalCategory P} (f : X ⟶ Z) (m : Y ⟶ Z) [Mono m]
    (h : imageCodes f ⊆ imageCodes m) : factorThroughMono f m h ≫ m=f := by
  apply WideSubcategory.hom_ext
  apply val_injective
  funext x
  apply Part.ext
  intro y
  change y ∈ val ((factorThroughMono f m h).hom ≫ m.hom) x ↔ y ∈ val f.hom x
  rw [mem_val_comp]
  constructor
  · rintro ⟨z,hz,hy⟩
    obtain ⟨u,hu,huz⟩ := (factorThroughMono_graph f m h x z).mp hz
    have he : u=y := Part.mem_unique huz hy
    exact he ▸ hu
  · intro hy
    obtain ⟨z,hz⟩ := h ⟨x,hy⟩
    exact ⟨z,(factorThroughMono_graph f m h x z).mpr ⟨y,hy,hz⟩,hz⟩

theorem imageCodes_subset_of_factor {X Y Z : TotalCategory P} (f : X ⟶ Z) (m : Y ⟶ Z)
    (k : X ⟶ Y) (hk : k ≫ m=f) : imageCodes f ⊆ imageCodes m := by
  rintro y ⟨x,hx⟩
  have hc : y ∈ val (k.hom ≫ m.hom) x := by
    change y ∈ val (k ≫ m).hom x
    rw [hk]
    exact hx
  obtain ⟨z,_,hz⟩ := (mem_val_comp _ _ x y).mp hc
  exact ⟨z,hz⟩

theorem factors_iff_imageCodes_subset {X Y Z : TotalCategory P} (f : X ⟶ Z) (m : Y ⟶ Z) [Mono m] :
    (∃ k : X ⟶ Y,k ≫ m=f) ↔ imageCodes f ⊆ imageCodes m :=
  ⟨fun ⟨k,hk⟩ => imageCodes_subset_of_factor f m k hk,
    fun h => ⟨factorThroughMono f m h,factorThroughMono_fac f m h⟩⟩

theorem mk_le_mk_iff_imageCodes_subset {X Y Z : TotalCategory P} (f : X ⟶ Z) (m : Y ⟶ Z)
    [Mono f] [Mono m] : Subobject.mk f ≤ Subobject.mk m ↔ imageCodes f ⊆ imageCodes m := by
  constructor
  · intro h
    exact imageCodes_subset_of_factor f m (Subobject.ofMkLEMk f m h)
      (Subobject.ofMkLEMk_comp h)
  · intro h
    exact Subobject.mk_le_mk_of_comm (factorThroughMono f m h) (factorThroughMono_fac f m h)

/-- Range inclusion gives an actual factor through the given image mono.
No program selecting derivations is required when the image is a theorem set. -/
theorem imageSubobject_le_mk_of_imageCodes_subset {X Y Z : TotalCategory P}
    (f : X ⟶ Z) (m : Y ⟶ Z) [Mono m] (h : imageCodes f ⊆ imageCodes m) :
    imageSubobject f ≤ Subobject.mk m :=
  imageSubobject_le_mk m f (factorThroughMono f m h) (factorThroughMono_fac f m h)

/-- The chosen categorical image may use different point coordinates.
Its inclusion nevertheless has exactly the original output words. -/
theorem imageCodes_image_ι {X Y : TotalCategory P} (f : X ⟶ Y) :
    imageCodes (image.ι f)=imageCodes f := by
  have hs : Surjective (factorThruImage f).hom :=
    (surjective_iff_range_top _).mpr
      ((regularEpi_iff_range_top _).mp (inferInstance : IsRegularEpi (factorThruImage f)))
  apply Set.Subset.antisymm
  · rintro y ⟨u,hu⟩
    obtain ⟨x,hx⟩ := hs u (val_source (image.ι f).hom u y hu)
    refine ⟨x,?_⟩
    have hc : y ∈ val (factorThruImage f ≫ image.ι f).hom x :=
      (mem_val_comp _ _ x y).mpr ⟨u,hx,hu⟩
    rwa [image.fac f] at hc
  · exact imageCodes_subset_of_factor f (image.ι f) (factorThruImage f) (image.fac f)

theorem imageSubobject_le_mk_iff {X Y Z : TotalCategory P} (f : X ⟶ Z) (m : Y ⟶ Z) [Mono m] :
    imageSubobject f ≤ Subobject.mk m ↔ imageCodes f ⊆ imageCodes m := by
  change Subobject.mk (image.ι f) ≤ Subobject.mk m ↔ _
  rw [mk_le_mk_iff_imageCodes_subset,imageCodes_image_ι]

/-- These are the actual regular images of the supplied maps, independently
of the chosen representation of either image object. -/
theorem imageSubobject_le_iff {X X' Y : TotalCategory P} (f : X ⟶ Y) (g : X' ⟶ Y) :
    imageSubobject f ≤ imageSubobject g ↔ imageCodes f ⊆ imageCodes g := by
  change imageSubobject f ≤ Subobject.mk (image.ι g) ↔ _
  rw [imageSubobject_le_mk_iff,imageCodes_image_ι]

theorem imageSubobject_eq_iff {X X' Y : TotalCategory P} (f : X ⟶ Y) (g : X' ⟶ Y) :
    imageSubobject f=imageSubobject g ↔ imageCodes f=imageCodes g := by
  constructor
  · intro h
    exact Set.Subset.antisymm ((imageSubobject_le_iff f g).mp h.le)
      ((imageSubobject_le_iff g f).mp h.ge)
  · intro h
    exact le_antisymm ((imageSubobject_le_iff f g).mpr h.le)
      ((imageSubobject_le_iff g f).mpr h.ge)

end CategoricalEssentialIncompleteness.V46.Miller.Total.Subobjects
