/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerTotalCarriers

/-! # The actual semidecidable presentation of the total splitting -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Total
variable {P : Uniform.Family}
attribute [instance 2000] Uniform.nativeRestriction

theorem inclusion_rst : PreservesRestriction (inclusion (P := P)) := by
  intro X Y f
  rfl

instance inclusion_essSurj : (inclusion (P := P)).EssSurj where
  mem_essImage Y := by
    let i := Uniform.codeIso Y.base
    let d := Idem.isoEquiv i Y.domain
    let A := Uniform.support d
    have hA : Uniform.Enumerable P (· ∈ A) := Uniform.support_enumerable d
    have hd : Uniform.setIdem (Uniform.N P) A hA = d := by
      apply Idem.ext
      apply Uniform.hom_ext_mem
      intro x y
      simp only [Uniform.mem_idem,Uniform.support_setIdem]
      rfl
    let X : Carrier P := ⟨A,hA⟩
    have hi : Y ≅ (⟨Uniform.N P,d⟩ : SplitObject (Uniform.Object P)) :=
      splitIsoOfComm i (by
        change Y.domain.hom ≫ i.hom = i.hom ≫ d.hom
        rw [show d = Idem.isoEquiv i Y.domain from rfl,Idem.isoEquiv_hom]
        simp only [← Category.assoc,Iso.hom_inv_id,Category.id_comp])
    have hx : (⟨Uniform.N P,d⟩ : SplitObject (Uniform.Object P)) = inclusion.obj X := by
      change (⟨Uniform.N P,d⟩ : SplitObject (Uniform.Object P)) =
        ⟨Uniform.N P,Uniform.setIdem (Uniform.N P) A hA⟩
      rw [hd]
    exact ⟨X,⟨(hi ≪≫ eqToIso hx).symm⟩⟩

instance inclusion_isEquivalence : (inclusion (P := P)).IsEquivalence := {}

def carrierEquivalence : Carrier P ≌ SplitObject (Uniform.Object P) := inclusion.asEquivalence

def totalEquivalence : TotalCategory P ≌ WideSubcategory (isTotal (C := SplitObject (Uniform.Object P))) :=
  inclusion_rst.totalEquivalence

abbrev CanonicalTotal (z : Point) :=
  WideSubcategory (isTotal (C := SplitObject (Uniform.PointObject z)))

def pointPresentation (z : Point) : PointTotal z ≌ CanonicalTotal z :=
  totalEquivalence (P := Uniform.Family.ofPoint z)

theorem pointPresentation_object (z : Point) (X : PointTotal z) :
    (pointPresentation z).functor.obj X =
      ⟨⟨Uniform.N (Uniform.Family.ofPoint z),
        Uniform.setIdem _ X.obj.support X.obj.enumerable⟩⟩ := rfl

theorem pointPresentation_value (z : Point) {X Y : PointTotal z} (f : X ⟶ Y) :
    ((pointPresentation z).functor.map f).hom.hom.val = val f.hom := rfl

end CategoricalEssentialIncompleteness.V46.Miller.Total
