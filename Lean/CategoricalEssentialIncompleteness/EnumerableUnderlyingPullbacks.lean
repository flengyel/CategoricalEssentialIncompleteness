/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.EnumerableUnderlying
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-! # The numerical underlying-set functor preserves total pullbacks -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableCarriers

theorem underlying_isPullback {P X Y Z : Total} {p : P ⟶ X} {q : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback p q f g) :
    IsPullback (underlying.map p) (underlying.map q) (underlying.map f) (underlying.map g) := by
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨(underlying.map_comp p f).symm.trans
    ((congrArg underlying.map h.w).trans (underlying.map_comp q g)),?_,?_⟩
  · intro w w' he
    have hp : point w.val w.property ≫ p=point w'.val w'.property ≫ p := by
      apply point_comp_eq p p w.val w'.val (underlying.map p w).val w.property w'.property
        (totalFunction_mem p w)
      rw [congrArg Subtype.val he.1]
      exact totalFunction_mem p w'
    have hq : point w.val w.property ≫ q=point w'.val w'.property ≫ q := by
      apply point_comp_eq q q w.val w'.val (underlying.map q w).val w.property w'.property
        (totalFunction_mem q w)
      rw [congrArg Subtype.val he.2]
      exact totalFunction_mem q w'
    have he := congrArg (fun k : singletonTotal ⟶ P => val k.hom 0) (h.hom_ext hp hq)
    rw [point_value w.val w.property 0 rfl,point_value w'.val w'.property 0 rfl] at he
    exact Subtype.ext (Part.some_injective he)
  · intro x y he
    have hg : (underlying.map f x).val ∈ val g.hom y.val := by
      rw [congrArg Subtype.val he]
      exact totalFunction_mem g y
    obtain ⟨w,hp,hq⟩ := pullback_lifts_elements h x.val y.val (underlying.map f x).val
      (totalFunction_mem f x) hg
    let w' : {n // n ∈ P.obj.support} := ⟨w,val_source p.hom w x.val hp⟩
    exact ⟨w',(totalFunction_eq_iff p w' x).mpr hp,(totalFunction_eq_iff q w' y).mpr hq⟩

instance underlying_preservesCospan {X Y Z : Total} (f : X ⟶ Z) (g : Y ⟶ Z) :
    PreservesLimit (cospan f g) underlying :=
  preservesLimit_of_preserves_limit_cone (IsPullback.of_hasPullback f g).isLimit
    ((isLimitMapConePullbackConeEquiv underlying pullback.condition).symm
      (underlying_isPullback (IsPullback.of_hasPullback f g)).isLimit)

instance underlying_preservesPullbacks : PreservesLimitsOfShape WalkingCospan underlying where
  preservesLimit := by
    intro K
    exact preservesLimit_of_iso_diagram underlying (diagramIsoCospan K).symm

end CategoricalEssentialIncompleteness.LocalConnectedness.EnumerableCarriers
