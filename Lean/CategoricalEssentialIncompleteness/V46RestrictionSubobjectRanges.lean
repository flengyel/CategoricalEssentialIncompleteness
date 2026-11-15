/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46BooleanPartialDecision
public import CategoricalEssentialIncompleteness.V46MonoInversesChoice
public import CategoricalEssentialIncompleteness.RestrictionSpanPullbacks
public import CategoricalEssentialIncompleteness.V46RegularImage

/-! # Regular subobjects, restriction ranges and total inverse images -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.RestrictionSubobjects
variable {C : Type u} [Category.{v} C] [RestrictionCategory C] [Splits C] [Ranges C]
variable (h : MonoInverses C)
variable [WeakChoice C]

theorem inverse_eq_span {X Y : Tot C} (m : X ⟶ Y) [Mono m] :
    inverse h m = PartialSpans.inverse m := by
  apply PartialMono.section_unique (PartialSpans.partialMono_of_mono m) _
    (PartialSpans.inverse_section m)
  constructor
  · exact inverse_hom h m
  · rw [← Category.assoc, hom_inverse, Category.id_comp]

omit [Splits C] [WeakChoice C] in
theorem domain_eq_range {X : Tot C} (A : Subobject X) :
    domain h A = Ranges.range A.arrow.hom := by
  apply SectionOf.domain
  constructor
  · exact inverse_hom h A.arrow
  · rw [← Category.assoc, hom_inverse, Category.id_comp]

variable [HasPullbacks (Tot C)]

theorem domain_pullback {X Y : Tot C} (f : X ⟶ Y) (A : Subobject Y) :
    domain h ((Subobject.pullback f).obj A) = Idem.pull f.hom (domain h A) := by
  have hp : (Subobject.pullback f).obj A = Subobject.mk (pullback.fst f A.arrow) := by
    calc
      _ = (Subobject.pullback f).obj (Subobject.mk A.arrow) := by rw [Subobject.mk_arrow]
      _ = _ := Subobject.pullback_obj_mk (IsPullback.of_hasPullback f A.arrow).flip
  rw [hp, BooleanPartialDecision.domain_mk, inverse_eq_span, domain]
  rw [inverse_eq_span]
  apply Idem.ext
  change rst (PartialSpans.inverse (pullback.fst f A.arrow)) =
    rst (f.hom ≫ rst (PartialSpans.inverse A.arrow))
  rw [← rst_comp_rst_right, ← PartialSpans.inverse_pullback_snd f A.arrow,
    rst_comp_of_isTotal _ (pullback.snd f A.arrow).property]

variable [Regular (Tot C)]

omit [WeakChoice C] [HasPullbacks (Tot C)] in
theorem domain_image {X Y : Tot C} (f : X ⟶ Y) :
    domain h (imageSubobject f) = Ranges.range f.hom := by
  let m := image.ι f
  let e := factorThruImage f
  have hi := LocalConnectedness.V46.range_regularImage e m (inverse h m)
    (hom_inverse h m) (inverse_hom h m)
  have hf : e.hom ≫ m.hom = f.hom := congrArg (fun k => k.hom) (image.fac f)
  rw [hf] at hi
  change domain h (Subobject.mk (image.ι f)) = _
  rw [BooleanPartialDecision.domain_mk]
  apply Idem.ext
  exact (inverse_hom h m).symm.trans hi.symm

end CategoricalEssentialIncompleteness.V46.RestrictionSubobjects
