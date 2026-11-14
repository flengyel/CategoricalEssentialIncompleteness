/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46MonicSpanValues
public import CategoricalEssentialIncompleteness.V46RestrictionRetraction
public import CategoricalEssentialIncompleteness.V46SubobjectInseparability

/-! # The Boolean partial morphism of a disjoint pair of subobjects -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.BooleanPartialDecision

open RestrictionSubobjects
variable {C : Type u} [Category.{v} C] [RestrictionCategory C]
variable [Regular (Tot C)] [FinitaryExtensive (Tot C)]
variable (inverses : MonoInverses C) {X : Tot C} (a b : Subobject X) (hab : a ⊓ b = ⊥)

def cover (_hab : a ⊓ b = ⊥) : (a : Tot C) ⨿ (b : Tot C) ⟶ X :=
  coprod.desc a.arrow b.arrow

instance cover_mono : Mono (cover a b hab) :=
  (PresentationLemmas.mono_copair_iff a.arrow b.arrow).mpr (by
    simpa only [Subobject.mk_arrow] using hab)

def values : (a : Tot C) ⨿ (b : Tot C) ⟶ Two (Tot C) :=
  coprod.desc (Two.constant _ true) (Two.constant _ false)

/-- The domain is the disjoint coproduct of the two subobjects; the right
leg gives true on the first summand and false on the second. -/
def decision : X.obj ⟶ (Two (Tot C)).obj :=
  inverse inverses (cover a b hab) ≫ (values a b).hom

theorem restriction : rst (decision inverses a b hab) =
    rst (inverse inverses (cover a b hab)) :=
  rst_comp_of_isTotal _ (values a b).property

theorem cover_decision : (cover a b hab).hom ≫ decision inverses a b hab = (values a b).hom := by
  rw [decision, ← Category.assoc, hom_inverse, Category.id_comp]

theorem cover_restriction : (cover a b hab).hom ≫ rst (decision inverses a b hab) =
    (cover a b hab).hom := by
  rw [restriction]
  exact MonicSpanValues.hom_restrict_inverse inverses _

theorem positive_value : a.arrow.hom ≫ decision inverses a b hab =
    (Two.constant (a : Tot C) true).hom := by
  have ha : (coprod.inl : (a : Tot C) ⟶ (a : Tot C) ⨿ (b : Tot C)).hom ≫
      (cover a b hab).hom = a.arrow.hom :=
    congrArg (fun k => k.hom) (coprod.inl_desc a.arrow b.arrow)
  rw [← ha, Category.assoc, cover_decision]
  exact congrArg (fun k => k.hom)
    (coprod.inl_desc (Two.constant (a : Tot C) true) (Two.constant (b : Tot C) false))

theorem negative_value : b.arrow.hom ≫ decision inverses a b hab =
    (Two.constant (b : Tot C) false).hom := by
  have hb : (coprod.inr : (b : Tot C) ⟶ (a : Tot C) ⨿ (b : Tot C)).hom ≫
      (cover a b hab).hom = b.arrow.hom :=
    congrArg (fun k => k.hom) (coprod.inr_desc a.arrow b.arrow)
  rw [← hb, Category.assoc, cover_decision]
  exact congrArg (fun k => k.hom)
    (coprod.inr_desc (Two.constant (a : Tot C) true) (Two.constant (b : Tot C) false))

theorem extension_iff (g : X.obj ⟶ (Two (Tot C)).obj) :
    rst (decision inverses a b hab) ≫ g = decision inverses a b hab ↔
      (cover a b hab).hom ≫ g = (values a b).hom := by
  constructor
  · intro h
    calc
      _ = ((cover a b hab).hom ≫ rst (decision inverses a b hab)) ≫ g := by
        rw [cover_restriction]
      _ = (cover a b hab).hom ≫ decision inverses a b hab := by rw [Category.assoc, h]
      _ = _ := cover_decision inverses a b hab
  · intro h
    rw [restriction, ← inverse_hom inverses (cover a b hab), Category.assoc, h]
    rfl

theorem hasTotalExtension_iff_separator :
    RestrictionRetraction.HasTotalExtension (decision inverses a b hab) ↔
      HasSubobjectSeparator a b := by
  rw [subobject_separator_iff_boolean]
  constructor
  · rintro ⟨g, hg, he⟩
    let d : X ⟶ Two (Tot C) := ⟨g, hg⟩
    have hd : cover a b hab ≫ d = values a b :=
      WideSubcategory.hom_ext _ ((extension_iff inverses a b hab g).mp he)
    refine ⟨d, ?_, ?_⟩
    · have h := congrArg (fun k => (coprod.inl : (a : Tot C) ⟶ _) ≫ k) hd
      simpa only [cover, values, ← Category.assoc, coprod.inl_desc] using h
    · have h := congrArg (fun k => (coprod.inr : (b : Tot C) ⟶ _) ≫ k) hd
      simpa only [cover, values, ← Category.assoc, coprod.inr_desc] using h
  · rintro ⟨d, ha, hb⟩
    refine ⟨d.hom, d.property, (extension_iff inverses a b hab d.hom).mpr ?_⟩
    have hd : cover a b hab ≫ d = values a b := by
      apply coprod.hom_ext
      · simpa only [cover, values, ← Category.assoc, coprod.inl_desc] using ha
      · simpa only [cover, values, ← Category.assoc, coprod.inr_desc] using hb
    exact congrArg (fun k => k.hom) hd

include hab in
theorem inseparable_iff_noTotalExtension :
    SubobjectInseparable a b ↔
      ¬ RestrictionRetraction.HasTotalExtension (decision inverses a b hab) :=
  ⟨fun h he => h.2 ((hasTotalExtension_iff_separator inverses a b hab).mp he),
    fun h => ⟨hab, fun hs => h ((hasTotalExtension_iff_separator inverses a b hab).mpr hs)⟩⟩

omit a b hab [Regular (Tot C)] [FinitaryExtensive (Tot C)] in
theorem domain_mk {A B : Tot C} (m : A ⟶ B) [Mono m] :
    domain inverses (Subobject.mk m) = Idem.ofRestrict (inverse inverses m) := by
  let j := Subobject.underlyingIso m
  have hj : j.hom.hom ≫ m.hom = (Subobject.mk m).arrow.hom :=
    congrArg (fun k => k.hom) (Subobject.underlyingIso_hom_comp_eq_mk m)
  have hi : j.inv.hom ≫ (Subobject.mk m).arrow.hom = m.hom := by
    rw [← hj, ← Category.assoc]
    have hh : j.inv.hom ≫ j.hom.hom = 𝟙 A.obj :=
      congrArg (fun k => k.hom) j.inv_hom_id
    rw [hh, Category.id_comp]
  apply le_antisymm
  · apply (domain_le_iff_fixed inverses _ _).mpr
    change (Subobject.mk m).arrow.hom ≫ rst (inverse inverses m) = _
    rw [← hj, Category.assoc, MonicSpanValues.hom_restrict_inverse]
  · apply Idem.le_def.mpr
    change rst (inverse inverses m) ≫ (domain inverses (Subobject.mk m)).hom = _
    have hm : m.hom ≫ (domain inverses (Subobject.mk m)).hom = m.hom := by
      rw [← hi, Category.assoc, inclusion_domain]
    rw [← inverse_hom inverses m, Category.assoc, hm]
    exact inverse_hom inverses m

theorem domain_eq : rst (decision inverses a b hab) = (domain inverses (a ⊔ b)).hom := by
  have hc : Subobject.mk (cover a b hab) = a ⊔ b := by
    have h : imageSubobject (cover a b hab) = a ⊔ b := by
      have h := PresentationLemmas.image_copair a.arrow b.arrow
      rw [imageSubobject_mono a.arrow, imageSubobject_mono b.arrow,
        Subobject.mk_arrow, Subobject.mk_arrow] at h
      exact h
    rwa [imageSubobject_mono] at h
  rw [restriction, ← hc, domain_mk]
  rfl

/-- The partial Boolean morphism is total precisely when its two domains
cover the sentence object. -/
theorem total_iff : isTotal (decision inverses a b hab) ↔ a ⊔ b = ⊤ := by
  constructor
  · intro ht
    have hr : isTotal (inverse inverses (cover a b hab)) :=
      (restriction inverses a b hab).symm.trans ht
    let r : X ⟶ (a : Tot C) ⨿ (b : Tot C) := ⟨inverse inverses (cover a b hab), hr⟩
    have hm : IsIso (cover a b hab) := ⟨⟨r,
      WideSubcategory.hom_ext _ (hom_inverse inverses _),
      WideSubcategory.hom_ext _ ((inverse_hom inverses _).trans hr)⟩⟩
    let := hm
    have h := (PresentationLemmas.image_eq_top_iff_regularEpi (cover a b hab)).mpr
      (inferInstance : IsRegularEpi (cover a b hab))
    simpa only [cover, PresentationLemmas.image_copair, imageSubobject_mono,
      Subobject.mk_arrow] using h
  · intro ht
    have hm : IsRegularEpi (cover a b hab) :=
      (PresentationLemmas.image_eq_top_iff_regularEpi _).mp (by
        simpa only [cover, PresentationLemmas.image_copair, imageSubobject_mono,
          Subobject.mk_arrow] using ht)
    let := hm
    let : IsIso (cover a b hab) :=
      isIso_of_regularEpi_of_mono _ (IsRegularEpi.getStruct _)
    have hi : (inv (cover a b hab)).hom ≫ (cover a b hab).hom = 𝟙 X.obj :=
      congrArg (fun k => k.hom) (IsIso.inv_hom_id (cover a b hab))
    have he : inverse inverses (cover a b hab) = (inv (cover a b hab)).hom := by
      have h := congrArg (fun k => (inv (cover a b hab)).hom ≫ k)
        (hom_inverse inverses (cover a b hab))
      simpa only [← Category.assoc, hi, Category.id_comp, Category.comp_id] using h
    rw [isTotal, restriction, he]
    exact (inv (cover a b hab)).property

end CategoricalEssentialIncompleteness.V46.BooleanPartialDecision
