/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.RestrictionFunctorEquivalences
import CategoricalEssentialIncompleteness.EnumerableCarriers
import CategoricalEssentialIncompleteness.ClassicalRecursionCategory

/-! # Numerical c.e. carriers realize the entire classical restriction splitting -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness

namespace EnumerableCarriers

open ClassicalPrograms PartialFunctions

theorem inclusion_rst : PreservesRestriction inclusion := by
  intro X Y f
  rfl

theorem inclusion_essSurj : inclusion.EssSurj where
  mem_essImage Y := by
    obtain ⟨i⟩ := RecursionCategory.Isotype.iso Y.base U
    let d := Idem.isoEquiv i Y.domain
    let A : Set ℕ := {n | (J.map d.hom n).Dom}
    have hA : REPred (fun n : ℕ => n ∈ A) := (omegaArrow_partrec d.hom).dom_re
    have hd : supportIdem A hA=d := by
      apply Idem.ext
      apply J.map_injective
      have he : inclusionRangeFunctor.mapIdem (supportIdem A hA)=
          inclusionRangeFunctor.mapIdem d := by
        rw [supportIdem_image]
        apply PartialFunctions.support_injective
        exact PartialFunctions.support_setIdem A
      exact congrArg Idem.hom he
    let X : Carrier := ⟨A,hA⟩
    have hi : Y ≅ (⟨U,d⟩ : SplitObject Rec) := splitIsoOfComm i (by
      change Y.domain.hom ≫ i.hom=i.hom ≫ d.hom
      rw [show d=Idem.isoEquiv i Y.domain from rfl,Idem.isoEquiv_hom]
      simp only [← Category.assoc,Iso.hom_inv_id,Category.id_comp])
    have hx : (⟨U,d⟩ : SplitObject Rec)=inclusion.obj X := by
      change (⟨U,d⟩ : SplitObject Rec)=⟨U,supportIdem A hA⟩
      rw [hd]
    exact ⟨X,⟨(hi ≪≫ eqToIso hx).symm⟩⟩

instance inclusion_isEquivalence : inclusion.IsEquivalence := by
  letI := inclusion_essSurj
  exact {}

def classicalSplitEquivalence : Carrier ≌ SplitObject Rec := inclusion.asEquivalence

end EnumerableCarriers
end CategoricalEssentialIncompleteness.LocalConnectedness
