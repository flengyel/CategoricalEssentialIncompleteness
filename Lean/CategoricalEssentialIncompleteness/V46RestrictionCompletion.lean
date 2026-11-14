/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.RestrictionFunctorEquivalences
public import CategoricalEssentialIncompleteness.LocalSwitch

/-! # Restriction completion from total retractions into a full subcategory -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v₁ v₂ u₁ u₂
open CategoryTheory CategoryTheory.RestrictionCategory
open CategoricalEssentialIncompleteness.LocalConnectedness

namespace CategoricalEssentialIncompleteness.V46.RestrictionCompletion

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
variable [RestrictionCategory A] [RestrictionCategory B]
variable (F : A ⥤ B) (hF : PreservesRestriction F)

structure Splitting (X : SplitObject A) where
  obj : B
  inclusion : obj ⟶ F.obj X.base
  retraction : F.obj X.base ⟶ obj
  total : isTotal inclusion
  section_eq : inclusion ≫ retraction = 𝟙 obj
  support_eq : retraction ≫ inclusion = F.map X.domain.hom

def chosenSplitting [Splits B] (X : SplitObject A) : Splitting F X := by
  let h := Splits.splitting (hF.mapIdem X.domain)
  let Z := Classical.choose h
  let hZ := Classical.choose_spec h
  let m := Classical.choose hZ
  let hm := Classical.choose_spec hZ
  let r := Classical.choose hm
  let hr := Classical.choose_spec hm
  exact ⟨Z, m, r, hr.1, hr.2.1, hr.2.2⟩

variable (s : ∀ X : SplitObject A, Splitting F X)

theorem inclusion_support (X : SplitObject A) :
    (s X).inclusion ≫ F.map X.domain.hom = (s X).inclusion := by
  rw [← (s X).support_eq, ← Category.assoc, (s X).section_eq, Category.id_comp]

theorem support_retraction (X : SplitObject A) :
    F.map X.domain.hom ≫ (s X).retraction = (s X).retraction := by
  rw [← (s X).support_eq, Category.assoc, (s X).section_eq, Category.comp_id]

def extension : SplitObject A ⥤ B where
  obj X := (s X).obj
  map {X Y} f := (s X).inclusion ≫ F.map f.hom ≫ (s Y).retraction
  map_id X := by
    change (s X).inclusion ≫ F.map X.domain.hom ≫ (s X).retraction = _
    rw [← Category.assoc, inclusion_support, (s X).section_eq]
  map_comp {X Y Z} f g := by
    change (s X).inclusion ≫ F.map (f.hom ≫ g.hom) ≫ (s Z).retraction = _
    rw [F.map_comp]
    simp only [Category.assoc]
    rw [← Category.assoc (s Y).retraction, (s Y).support_eq]
    have he : F.map Y.domain.hom ≫ F.map g.hom = F.map g.hom := by
      rw [← F.map_comp, g.source]
    rw [← Category.assoc (F.map Y.domain.hom), he]

include hF in
theorem extension_restriction : PreservesRestriction (extension F s) := by
  intro X Y f
  change (s X).inclusion ≫ F.map (rst f.hom) ≫ (s X).retraction =
    rst ((s X).inclusion ≫ F.map f.hom ≫ (s Y).retraction)
  rw [hF f.hom]
  have ht : F.map f.hom ≫ F.map Y.domain.hom = F.map f.hom := by
    rw [← F.map_comp, f.target]
  calc
    _ = (rst ((s X).inclusion ≫ F.map f.hom) ≫ (s X).inclusion) ≫
        (s X).retraction := by rw [rst_comp, Category.assoc]
    _ = rst ((s X).inclusion ≫ F.map f.hom) := by
      rw [Category.assoc, (s X).section_eq, Category.comp_id]
    _ = rst (((s X).inclusion ≫ F.map f.hom ≫ (s Y).retraction) ≫
        (s Y).inclusion) := by simp only [Category.assoc, (s Y).support_eq, ht]
    _ = _ := rst_comp_of_isTotal _ (s Y).total

theorem recover_map {X Y : SplitObject A} (f : X ⟶ Y) :
    (s X).retraction ≫ (extension F s).map f ≫ (s Y).inclusion = F.map f.hom := by
  change (s X).retraction ≫ ((s X).inclusion ≫ F.map f.hom ≫
    (s Y).retraction) ≫ (s Y).inclusion = _
  simp only [← Category.assoc, (s X).support_eq]
  rw [← F.map_comp, f.source, Category.assoc, (s Y).support_eq, ← F.map_comp, f.target]

instance extension_faithful [F.Faithful] : (extension F s).Faithful where
  map_injective {X Y} f g he := by
    apply SplitObject.Hom.ext
    apply F.map_injective
    rw [← recover_map F s f, ← recover_map F s g, he]

instance extension_full [F.Full] [F.Faithful] : (extension F s).Full where
  map_surjective {X Y} h := by
    change (s X).obj ⟶ (s Y).obj at h
    let f : X ⟶ Y := ⟨F.preimage ((s X).retraction ≫ h ≫ (s Y).inclusion), by
      apply F.map_injective
      rw [F.map_comp, F.map_preimage, ← Category.assoc, support_retraction], by
      apply F.map_injective
      rw [F.map_comp, F.map_preimage, Category.assoc, Category.assoc, inclusion_support]⟩
    refine ⟨f, ?_⟩
    change (s X).inclusion ≫ F.map f.hom ≫ (s Y).retraction = h
    rw [show F.map f.hom = (s X).retraction ≫ h ≫ (s Y).inclusion from F.map_preimage _]
    simp only [← Category.assoc, (s X).section_eq, Category.id_comp]
    rw [Category.assoc, (s Y).section_eq, Category.comp_id]

variable [F.Full] [F.Faithful]

include hF in
theorem extension_essSurj
    (dense : ∀ Y : B, ∃ (X : A) (j : Y ⟶ F.obj X) (r : F.obj X ⟶ Y),
      isTotal j ∧ j ≫ r = 𝟙 Y ∧ r ≫ j = rst r) : (extension F s).EssSurj where
  mem_essImage Y := by
    obtain ⟨X, j, r, _, hjr, hrj⟩ := dense Y
    let a : Idem X := ⟨F.preimage (rst r), by
      apply F.map_injective
      rw [hF _, F.map_preimage, restrict_restrict]⟩
    let X' : SplitObject A := ⟨X, a⟩
    have ha : F.map X'.domain.hom = r ≫ j := (F.map_preimage _).trans hrj.symm
    refine ⟨X', ⟨{
      hom := (s X').inclusion ≫ r
      inv := j ≫ (s X').retraction
      hom_inv_id := by
        change ((s X').inclusion ≫ r) ≫ (j ≫ (s X').retraction) = 𝟙 (s X').obj
        rw [Category.assoc, ← Category.assoc r, ← ha, ← Category.assoc,
          inclusion_support, (s X').section_eq]
      inv_hom_id := by
        rw [Category.assoc, ← Category.assoc (s X').retraction, (s X').support_eq, ha,
          ← Category.assoc, ← Category.assoc, hjr, Category.id_comp, hjr]
    }⟩⟩

def equivalence [Splits B]
    (dense : ∀ Y : B, ∃ (X : A) (j : Y ⟶ F.obj X) (r : F.obj X ⟶ Y),
      isTotal j ∧ j ≫ r = 𝟙 Y ∧ r ≫ j = rst r) : SplitObject A ≌ B := by
  let s := chosenSplitting F hF
  letI := extension_essSurj F hF s dense
  letI : (extension F s).IsEquivalence := {}
  exact (extension F s).asEquivalence

theorem equivalence_restriction [Splits B]
    (dense : ∀ Y : B, ∃ (X : A) (j : Y ⟶ F.obj X) (r : F.obj X ⟶ Y),
      isTotal j ∧ j ≫ r = 𝟙 Y ∧ r ≫ j = rst r) :
    PreservesRestriction (equivalence F hF dense).functor :=
  extension_restriction F hF (chosenSplitting F hF)

end CategoricalEssentialIncompleteness.V46.RestrictionCompletion

namespace CategoricalEssentialIncompleteness.V46.RestrictionCompletion

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Category.{v₂} B]
variable [RestrictionCategory A] [RestrictionCategory B]

theorem rst_iso_comp {X X' Y : B} (i : X ≅ X') (f : X' ⟶ Y) :
    rst (i.hom ≫ f) = i.hom ≫ rst f ≫ i.inv := by
  have h := congrArg (fun k => k ≫ i.inv) (rst_comp i.hom f)
  simpa only [Category.assoc, i.hom_inv_id, Category.comp_id] using h

theorem inverse_restriction (e : A ≌ B) (hF : PreservesRestriction e.functor) :
    PreservesRestriction e.inverse := by
  intro X Y f
  apply e.functor.map_injective
  have map_formula {U V : B} (g : U ⟶ V) :
      e.functor.map (e.inverse.map g) =
        (e.counitIso.app U).hom ≫ g ≫ (e.counitIso.app V).inv := by
    change e.functor.map (e.inverse.map g) =
      e.counitIso.hom.app U ≫ g ≫ e.counitIso.inv.app V
    have h := congrArg (fun k => k ≫ e.counitIso.inv.app V) (e.counitIso.hom.naturality g)
    simpa only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
      CategoryTheory.Functor.comp_map, CategoryTheory.Functor.id_map] using h
  rw [hF _, map_formula, map_formula]
  have ht : isTotal (e.counitIso.app Y).inv := iso_total (e.counitIso.app Y).symm
  rw [← Category.assoc (e.counitIso.app X).hom f (e.counitIso.app Y).inv]
  rw [rst_comp_of_isTotal _ ht, rst_iso_comp]

end CategoricalEssentialIncompleteness.V46.RestrictionCompletion
