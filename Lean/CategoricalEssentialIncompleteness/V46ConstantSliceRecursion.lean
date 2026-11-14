/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46ConstantSlice
public import CategoricalEssentialIncompleteness.V46RestrictionProductZeros
public import CategoricalEssentialIncompleteness.V46AmbientProductTuring
public import PCats.DomSemilattice

/-! # The recursion category of original constant families over T -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory PCategoryStruct
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.ConstantSlice

open RestrictionSubobjects RecursionCategory
variable {R : Type u} [Category.{v} R] [PCategoryStruct R] [PCategory R]
variable [HasZeroMorphisms R] [Prodominical R] [Isotype R]
attribute [local instance] SplitObject.productData SplitObject.productLaws SplitObject.productSplits
attribute [local instance] SplitObject.prodominicalLaws

local instance recursionBaseRestriction : RestrictionCategory (SplitObject R) :=
  @PCategory.inducedRestriction (SplitObject R) inferInstance
    SplitObject.productData SplitObject.productLaws

local instance baseZero : RestrictionZero (SplitObject R) where
  restrict_zero X Y := by
    change PCategoryStruct.rst (0 : X ⟶ Y) = 0
    exact DomSemilattice.rst_zero X Y

instance zeros (T : SplitObject R) : HasZeroMorphisms (ConstantCategory T) where
  zero X Y := ⟨InducedCategory.homMk ⟨0, by
    rw [zero_comp, RestrictionZero.restrict_zero, zero_comp]⟩⟩
  comp_zero := by intros; apply InducedCategory.hom_ext; exact AmbientPartialSlice.Hom.ext comp_zero
  zero_comp := by intros; apply InducedCategory.hom_ext; exact AmbientPartialSlice.Hom.ext zero_comp

instance restrictionZero (T : SplitObject R) : RestrictionZero (ConstantCategory T) where
  restrict_zero _X _Y := InducedCategory.hom_ext
    (AmbientPartialSlice.Hom.ext (RestrictionZero.restrict_zero _ _))

variable [HasPullbacks (Tot (SplitObject R))]

omit [Isotype R] in
theorem prodominical (T : SplitObject R) :
    @Prodominical (ConstantCategory T) inferInstance (productData T) inferInstance :=
  (restrictionProducts T).prodominicalLaws

theorem exists_evaluator (rec : PRecursionCategory R) (T : SplitObject R) :
    ∃ τ : (restrictionProducts T).prod (rec.W : ConstantCategory T) rec.W ⟶ rec.W,
      @IsTuringMorphism (ConstantCategory T) inferInstance (productData T) (productLaws T)
        rec.W rec.W rec.W τ := by
  let Q := (splittingInclusion (C := R)).obj rec.W
  obtain ⟨τ, hτ⟩ := SplitTuring.turingFamily rec Q Q
  let D := AmbientSliceProducts.restrictionProducts T
  let e := AmbientProductTuring.evaluator T τ
  have he := AmbientProductTuring.evaluator_isTuring T τ hτ
  exact ⟨FullRestrictionProducts.evaluator (inclusion T) D
      (fun X Y => (nearProd X Y : R)) (productIso T) (rec.W : ConstantCategory T) e,
    FullRestrictionProducts.evaluator_isTuring (inclusion T) (inclusion_restriction T) D
      (fun X Y => (nearProd X Y : R)) (productIso T) (rec.W : ConstantCategory T) e he⟩

@[instance_reducible] def recursionCategory (rec : PRecursionCategory R) (T : SplitObject R) :
    @PRecursionCategory (ConstantCategory T) inferInstance (productData T) (productLaws T)
      inferInstance (prodominical T) (isotype T) := by
  let : PCategoryStruct (ConstantCategory T) := productData T
  let : PCategory (ConstantCategory T) := productLaws T
  let : Prodominical (ConstantCategory T) := prodominical T
  exact {
    W := rec.W
    X := rec.W
    Y := rec.W
    tau := Classical.choose (exists_evaluator rec T)
    is_turing := Classical.choose_spec (exists_evaluator rec T)
  }

end CategoricalEssentialIncompleteness.V46.ConstantSlice
