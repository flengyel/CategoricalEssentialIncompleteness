/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MillerTotalSubobjectOrder


/-! # Statement checks in `V46MillerTotalSubobjectOrderChecks` -/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Total.Subobjects.Checks

example {P : Uniform.Family} {X Y : TotalCategory P} (m : X ⟶ Y) [Mono m] (y x : ℕ) :
    x ∈ val (PartialSpans.inverse m) y ↔ y ∈ val m.hom x := inverse_graph m y x

example {P : Uniform.Family} {X Y Z : TotalCategory P} (f : X ⟶ Z) (m : Y ⟶ Z) [Mono m]
    (h : imageCodes f ⊆ imageCodes m) :
    ∃ k : X ⟶ Y,k ≫ m=f :=
  ⟨factorThroughMono f m h,factorThroughMono_fac f m h⟩

example {P : Uniform.Family} {X Y Z : TotalCategory P} (f : X ⟶ Z) (m : Y ⟶ Z)
    [Mono f] [Mono m] : Subobject.mk f ≤ Subobject.mk m ↔ imageCodes f ⊆ imageCodes m :=
  mk_le_mk_iff_imageCodes_subset f m

example {P : Uniform.Family} {X Y Z : TotalCategory P} (f : X ⟶ Z) (m : Y ⟶ Z) [Mono m]
    (h : imageCodes f ⊆ imageCodes m) : imageSubobject f ≤ Subobject.mk m :=
  imageSubobject_le_mk_of_imageCodes_subset f m h

example {P : Uniform.Family} {X Y : TotalCategory P} (f : X ⟶ Y) :
    imageCodes (image.ι f)=imageCodes f := imageCodes_image_ι f

example {P : Uniform.Family} {X X' Y : TotalCategory P} (f : X ⟶ Y) (g : X' ⟶ Y) :
    imageSubobject f ≤ imageSubobject g ↔ imageCodes f ⊆ imageCodes g :=
  imageSubobject_le_iff f g

example {P : Uniform.Family} {X X' Y : TotalCategory P} (f : X ⟶ Y) (g : X' ⟶ Y) :
    imageSubobject f=imageSubobject g ↔ imageCodes f=imageCodes g :=
  imageSubobject_eq_iff f g

end CategoricalEssentialIncompleteness.V46.Miller.Total.Subobjects.Checks
