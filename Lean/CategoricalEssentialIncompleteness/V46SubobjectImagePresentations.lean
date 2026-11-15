/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46SubobjectInseparability

/-! # Regular images of coproduct presentations and subobject direct images -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.V46.SubobjectImagePresentations
variable {D : Type u} [Category.{v} D] [Regular D] [FinitaryExtensive D]

omit [FinitaryExtensive D] in
/-- Subobject direct image is the regular image of its inclusion composite. -/
theorem exists_eq_image {X Y : D} (f : X ⟶ Y) (A : Subobject X) :
    (Subobject.«exists» f).obj A = imageSubobject (A.arrow ≫ f) := by
  apply le_antisymm
  · exact Subobject.exists_le_of_comm f (factorThruImageSubobject (A.arrow ≫ f))
      (imageSubobject_arrow_comp (A.arrow ≫ f))
  · let F := Subobject.imageFactorisation f A
    exact imageSubobject_le (A.arrow ≫ f) F.F.e F.F.fac

omit [FinitaryExtensive D] in
/-- The choice of representative for a monic subobject does not change
its direct image. -/
theorem exists_mk {A X Y : D} (m : A ⟶ X) [Mono m] (f : X ⟶ Y) :
    (Subobject.«exists» f).obj (Subobject.mk m) = imageSubobject (m ≫ f) := by
  rw [exists_eq_image, ← Subobject.underlyingIso_hom_comp_eq_mk m,
    Category.assoc, imageSubobject_iso_comp]

end CategoricalEssentialIncompleteness.V46.SubobjectImagePresentations
