/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46CompatiblePartialSlices
public import CategoricalEssentialIncompleteness.V46ConstantSliceFull
public import CategoricalEssentialIncompleteness.V46SplitSliceTuring
public import CategoricalEssentialIncompleteness.V46OriginalConstantFunctor

/-! # The full recursion subcategory with the chosen total restriction structure -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory PCategoryStruct
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.CompatibleSplitSlices
open RestrictionSubobjects RecursionCategory
variable {R : Type u} [Category.{v} R] [PCategoryStruct R] [PCategory R]
local instance : PCategoryStruct (SplitObject R) := SplitObject.productData
local instance : PCategory (SplitObject R) := SplitObject.productLaws
variable [ρ : RestrictionCategory (SplitObject R)] (hρ : PCategory.inducedRestriction = ρ)
variable [Splits (SplitObject R)] [HasPullbacks (Tot (SplitObject R))]

omit [Splits (SplitObject R)] in
include hρ in
theorem pullbacks :
    HasPullbacks (@Tot (SplitObject R) inferInstance PCategory.inducedRestriction) := by
  rw [hρ]
  infer_instance

variable [HasZeroMorphisms R] [Prodominical R] [Isotype R]
variable (inverses : MonoInverses (SplitObject R)) (T : Tot (SplitObject R))

/-- The literal full constant-object subcategory has its previously
constructed recursion-category structure for the actual base object. -/
@[instance_reducible] def recursionCategory (rec : PRecursionCategory R) :
    letI := pullbacks hρ
    @PRecursionCategory (ConstantSlice.Full.FullCategory T.obj) inferInstance
      (ConstantSlice.Full.productData T.obj) (ConstantSlice.Full.productLaws T.obj)
      inferInstance (ConstantSlice.Full.prodominical T.obj) (ConstantSlice.Full.isotype T.obj) := by
  subst ρ
  exact ConstantSlice.Full.recursionCategory rec T.obj

def inclusion : ConstantSlice.Full.FullCategory T.obj ⥤ PartialMaps.Par (Over T) := by
  subst ρ
  exact ConstantSlice.Full.actualInclusion inverses T

omit [HasZeroMorphisms R] [Prodominical R] [Isotype R] in
theorem inclusion_full : (inclusion hρ inverses T).Full := by
  subst ρ
  exact ConstantSlice.Full.actualInclusion_full inverses T

omit [HasZeroMorphisms R] [Prodominical R] [Isotype R] in
theorem inclusion_faithful : (inclusion hρ inverses T).Faithful := by
  subst ρ
  exact ConstantSlice.Full.actualInclusion_faithful inverses T

/-- Restriction splitting recovers every actual partial-map slice object. -/
def splittingEquivalence (Q : R) :
    SplitObject (ConstantSlice.Full.FullCategory T.obj) ≌ PartialMaps.Par (Over T) := by
  subst ρ
  exact ConstantSlice.Full.splittingEquivalence inverses T Q

/-- A split Turing category includes a universal object: every object is a
restriction retract of it by a total embedding. -/
structure TuringData (D : Type u) [Category.{v} D] [RestrictionCategory D] where
  products : PCategoryStruct D
  laws : @PCategory D inferInstance products
  restriction_eq : @PCategory.inducedRestriction D inferInstance products laws = (inferInstance : RestrictionCategory D)
  Q : D
  evaluator : @PCategoryStruct.nearProd D inferInstance products Q Q ⟶ Q
  turing : @IsTuringMorphism D inferInstance products laws Q Q Q evaluator
  universal : ∀ X : D, ∃ (j : X ⟶ Q) (s : Q ⟶ X),
    isTotal j ∧ j ≫ s = 𝟙 X ∧ s ≫ j = CategoryTheory.RestrictionCategory.rst s
  splittings : Splits D

/-- The chosen product structure agrees with the actual partial-map
restriction, and every actual slice object embeds into the Turing object. -/
def turingData (rec : PRecursionCategory R) : TuringData (PartialMaps.Par (Over T)) := by
  subst ρ
  let ex := SplitSliceTuring.turing_object inverses T rec
  let τ := Classical.choose ex
  have hτ := Classical.choose_spec ex
  exact {
    products := PartialSliceProducts.pcategoryStruct inverses T
    laws := PartialSliceProducts.pcategoryLaws inverses T
    restriction_eq := PartialSliceProducts.restrictionCategory_eq inverses T
    Q := PartialSliceTuring.constantObject T ((splittingInclusion (C := R)).obj rec.W)
    evaluator := SliceProductTuring.evaluator inverses T τ
    turing := hτ.2.1
    universal := hτ.2.2
    splittings := inferInstance
  }

omit [HasZeroMorphisms R] [Prodominical R] [Isotype R] in
include hρ inverses in
/-- The original-source functor is faithful for the actual total structure. -/
theorem original_faithful {Z : Tot (SplitObject R)} (point : Z ⟶ T) (hZ : IsTerminal Z) :
    (OriginalConstantFunctor.functor T.obj).Faithful := by
  subst ρ
  exact OriginalConstantFunctor.faithful inverses point hZ

omit [HasZeroMorphisms R] [Prodominical R] [Isotype R] in
theorem inclusion_range (Z : PartialMaps.Par (Over T)) :
    (∃ X : ConstantSlice.Full.FullCategory T.obj, (inclusion hρ inverses T).obj X = Z) ↔
      ∃ X : R, (inclusion hρ inverses T).obj (ConstantSlice.Full.object T.obj X) = Z := by
  subst ρ
  exact ConstantSlice.Full.actualInclusion_range inverses T Z

end CategoricalEssentialIncompleteness.V46.CompatibleSplitSlices
