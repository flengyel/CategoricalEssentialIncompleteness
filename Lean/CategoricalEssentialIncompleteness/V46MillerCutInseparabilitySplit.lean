/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerCategoryRelative
import CategoricalEssentialIncompleteness.V46SplitCoproducts
import CategoricalEssentialIncompleteness.V46SplitSplittings

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # The actual full fixed-oracle restriction splitting and inclusion

This uses the full singleton-family Rec^p, already compared with ordinary
relative recursiveness. The structures below come from the existing generic
restriction splitting; no split-target structures are added as hypotheses.
-/
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.Miller.CutInseparability

attribute [instance 2000] Uniform.nativeRestriction

abbrev SplitRelative (p : Bits) := SplitObject (Uniform.RelativeObject p)

def relativeInclusion (p : Bits) : Uniform.RelativeObject p ⥤ SplitRelative p :=
  splittingInclusion

instance (p : Bits) : (relativeInclusion p).Faithful where
  map_injective h := congrArg SplitObject.Hom.hom h

instance (p : Bits) : (relativeInclusion p).Full where
  map_surjective f := ⟨f.hom,SplitObject.Hom.ext rfl⟩

private theorem inclusion_comparison_hom (p : Bits) (X Y : Uniform.RelativeObject p) :
    (coproductComparison (relativeInclusion p) X Y).hom = 𝟙 (coprod X Y) := by
  apply CategoryTheory.HasCoproducts.hom_ext
  · have h := congrArg SplitObject.Hom.hom
      (i0_copair ((relativeInclusion p).map (i0 X Y)) ((relativeInclusion p).map (i1 X Y)))
    simpa only [coproductComparison,relativeInclusion,splittingInclusion,SplitObject.comp_hom,
      SplitObject.coproductInl_hom,Idem.top_hom,Category.id_comp,Category.comp_id] using h
  · have h := congrArg SplitObject.Hom.hom
      (i1_copair ((relativeInclusion p).map (i0 X Y)) ((relativeInclusion p).map (i1 X Y)))
    simpa only [coproductComparison,relativeInclusion,splittingInclusion,SplitObject.comp_hom,
      SplitObject.coproductInr_hom,Idem.top_hom,Category.id_comp,Category.comp_id] using h

private def inclusion_comparison_iso (p : Bits) (X Y : Uniform.RelativeObject p) :
    coprod ((relativeInclusion p).obj X) ((relativeInclusion p).obj Y) ≅
      (relativeInclusion p).obj (coprod X Y) where
  hom := coproductComparison (relativeInclusion p) X Y
  inv := ⟨𝟙 (coprod X Y),by
    change (𝟙 (coprod X Y)) ≫ 𝟙 (coprod X Y) = 𝟙 (coprod X Y)
    exact Category.id_comp _,by
    change (𝟙 (coprod X Y)) ≫ coprod_map (𝟙 X) (𝟙 Y) = 𝟙 (coprod X Y)
    rw [coprod_id,Category.id_comp]⟩
  hom_inv_id := SplitObject.Hom.ext (by
    change (coproductComparison (relativeInclusion p) X Y).hom ≫ 𝟙 (coprod X Y) =
      coprod_map (𝟙 X) (𝟙 Y)
    rw [coprod_id]
    exact (congrArg (fun f:coprod X Y⟶coprod X Y => f ≫ 𝟙 (coprod X Y))
      (inclusion_comparison_hom p X Y)).trans (Category.id_comp _))
  inv_hom_id := SplitObject.Hom.ext (by
    change (𝟙 (coprod X Y)) ≫ (coproductComparison (relativeInclusion p) X Y).hom =
      𝟙 (coprod X Y)
    exact (congrArg (fun f:coprod X Y⟶coprod X Y => (𝟙 (coprod X Y)) ≫ f)
      (inclusion_comparison_hom p X Y)).trans (Category.id_comp _))

/-- The printed I_p is a faithful full range functor into the actual
restriction splitting of the full fixed-oracle category. -/
def I (p : Bits) : RangeFunctor (Uniform.RelativeObject p) (SplitRelative p) where
  toFunctor := relativeInclusion p
  map_restrict _f := SplitObject.Hom.ext rfl
  map_range _f := SplitObject.Hom.ext rfl
  map_zero _X _Y := SplitObject.Hom.ext rfl
  comparison_isIso X Y := (inclusion_comparison_iso p X Y).isIso_hom

instance (p : Bits) : (I p).toFunctor.Faithful := inferInstanceAs ((relativeInclusion p).Faithful)
instance (p : Bits) : (I p).toFunctor.Full := inferInstanceAs ((relativeInclusion p).Full)

theorem I_value (p : Bits) {X Y : Uniform.RelativeObject p} (f : X ⟶ Y) :
    ((I p).toFunctor.map f).hom = f := rfl

theorem I_nonzero (p : Bits) :
    (I p).toFunctor.map (𝟙 (Uniform.N (Uniform.Family.singleton p))) ≠ 0 := by
  intro h
  have h₀ := congrArg (fun f => f.hom.val (0 : ℕ)) h
  change Part.some (0 : ℕ) = Part.none at h₀
  have hm := Part.mem_some (0 : ℕ)
  rw [h₀] at hm
  exact hm.1

end CategoricalEssentialIncompleteness.V46.Miller.CutInseparability
