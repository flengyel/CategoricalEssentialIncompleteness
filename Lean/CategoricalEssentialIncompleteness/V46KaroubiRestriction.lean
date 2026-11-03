/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46Karoubi

/-! # Restrictions on the Karoubi envelope of all idempotents -/

universe v u

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.Idempotents

namespace CategoricalEssentialIncompleteness.LocalConnectedness.V46

variable {C : Type u} [Category.{v} C] [RestrictionCategory C]

namespace KaroubiRestriction

/-- The source idempotent commutes with the underlying domain of a
Karoubi morphism, even when the source idempotent is not a restriction. -/
theorem source_comm {P Q : Karoubi C} (f : P ⟶ Q) :
    rst f.f ≫ P.p = P.p ≫ rst f.f := by
  have h := rst_comp P.p f.f
  rw [Karoubi.p_comp] at h
  exact h

/-- The manuscript formula is `bar(f)e`, which in diagrammatic
composition is `e ≫ rst f`. -/
def restriction {P Q : Karoubi C} (f : P ⟶ Q) : P ⟶ P :=
  ⟨P.p ≫ rst f.f, by
    simp only [← Category.assoc, P.idem]
    rw [Category.assoc, source_comm, ← Category.assoc, P.idem]⟩

@[simp] theorem restriction_f {P Q : Karoubi C} (f : P ⟶ Q) :
    (restriction f).f = P.p ≫ rst f.f := rfl

theorem underlying_domain {P Q : Karoubi C} (f : P ⟶ Q) :
    rst (restriction f).f = rst f.f := by
  change rst (P.p ≫ rst f.f) = rst f.f
  rw [← rst_comp_rst_right, Karoubi.p_comp]

theorem compose_domains {P Q R : Karoubi C} (f : P ⟶ Q) (g : P ⟶ R) :
    (P.p ≫ rst f.f) ≫ (P.p ≫ rst g.f) = P.p ≫ (rst f.f ≫ rst g.f) := by
  calc
    _ = P.p ≫ ((rst f.f ≫ P.p) ≫ rst g.f) := by simp only [Category.assoc]
    _ = P.p ≫ ((P.p ≫ rst f.f) ≫ rst g.f) := by rw [source_comm]
    _ = _ := by simp only [← Category.assoc, P.idem]

instance : RestrictionCategory (Karoubi C) where
  rst := restriction
  rst_comp_self f := by
    apply Karoubi.hom_ext
    change (_ ≫ rst f.f) ≫ f.f = f.f
    rw [Category.assoc, rst_comp_self, Karoubi.p_comp]
  rst_comm {X Y Z} f g := by
    apply Karoubi.hom_ext
    change (X.p ≫ rst f.f) ≫ (X.p ≫ rst g.f) =
      (X.p ≫ rst g.f) ≫ (X.p ≫ rst f.f)
    rw [compose_domains, compose_domains, rst_comm]
  rst_comp_rst {X Y Z} f g := by
    apply Karoubi.hom_ext
    change X.p ≫ rst ((X.p ≫ rst f.f) ≫ g.f) =
      (X.p ≫ rst f.f) ≫ (X.p ≫ rst g.f)
    have h : (X.p ≫ rst f.f) ≫ g.f = rst f.f ≫ g.f := by
      rw [← source_comm, Category.assoc, Karoubi.p_comp]
    rw [h, rst_comp_rst, compose_domains]
  rst_comp {X Y Z} f g := by
    apply Karoubi.hom_ext
    change (X.p ≫ rst (f.f ≫ g.f)) ≫ f.f = f.f ≫ (Y.p ≫ rst g.f)
    rw [Category.assoc, rst_comp, ← Category.assoc, Karoubi.p_comp,
      ← Category.assoc, Karoubi.comp_p]

@[simp] theorem rst_f {P Q : Karoubi C} (f : P ⟶ Q) :
    (rst f).f = P.p ≫ rst f.f := rfl

/-- The ordinary fully faithful inclusion also preserves restrictions. -/
theorem toKaroubi_preserves {X Y : C} (f : X ⟶ Y) :
    (toKaroubi C).map (rst f) = rst ((toKaroubi C).map f) := by
  apply Karoubi.hom_ext
  change rst f = (𝟙 X) ≫ rst f
  rw [Category.id_comp]

end KaroubiRestriction

/-- Restriction of a morphism conjugated by total isomorphisms. -/
theorem restriction_conjugate {X Y Z W : C} (i : X ≅ Y) (f : Y ⟶ Z) (j : Z ≅ W) :
    rst ((i.hom ≫ f) ≫ j.hom) = (i.hom ≫ rst f) ≫ i.inv := by
  rw [rst_comp_of_isTotal _ (iso_total j)]
  have h := congrArg (fun k => k ≫ i.inv) (rst_comp i.hom f)
  simpa only [Category.assoc, i.hom_inv_id, Category.comp_id] using h

variable {D : Type*} [Category D] [RestrictionCategory D]

/-- A natural isomorphism transfers restriction preservation. -/
theorem preserves_restrictions_of_iso {F G : C ⥤ D} (η : F ≅ G)
    (hG : ∀ {X Y : C} (f : X ⟶ Y), G.map (rst f) = rst (G.map f))
    {X Y : C} (f : X ⟶ Y) : F.map (rst f) = rst (F.map f) := by
  have map_eq {A B : C} (g : A ⟶ B) :
      F.map g = (η.hom.app A ≫ G.map g) ≫ η.inv.app B := by
    have h := congrArg (fun k => k ≫ η.inv.app B) (η.hom.naturality g)
    simpa only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id] using h
  have hr := restriction_conjugate (η.app X) (G.map f) (η.app Y).symm
  change rst ((η.hom.app X ≫ G.map f) ≫ η.inv.app Y) =
    (η.hom.app X ≫ rst (G.map f)) ≫ η.inv.app X at hr
  rw [map_eq f, hr, map_eq (rst f), hG]

/-- An equivalence preserving restrictions has an inverse preserving them. -/
theorem equivalence_inverse_preserves (E : C ≌ D)
    (hE : ∀ {X Y : C} (f : X ⟶ Y),
      E.functor.map (rst f) = rst (E.functor.map f))
    {X Y : D} (f : X ⟶ Y) :
    E.inverse.map (rst f) = rst (E.inverse.map f) := by
  apply E.functor.map_injective
  rw [hE]
  exact preserves_restrictions_of_iso E.counitIso (fun _ => rfl) f

end CategoricalEssentialIncompleteness.LocalConnectedness.V46

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork.Recursion

/-- The extension of the full fork inclusion to all idempotents
preserves the restriction operation. -/
theorem karoubiInclusion_preserves_restrictions {P Q : Karoubi Rec} (f : P ⟶ Q) :
    karoubiInclusion.map (rst f) = rst (karoubiInclusion.map f) := by
  apply Karoubi.hom_ext
  change (P.p ≫ rst f.f).hom = P.p.hom ≫ rst f.f.hom
  rw [show (P.p ≫ rst f.f).hom = P.p.hom ≫ (rst f.f).hom from rfl]
  rw [restriction_hom]

/-- The actual equivalence to natural partial fork maps preserves
restrictions, including at arbitrary idempotents of the Karoubi envelope. -/
theorem karoubiEquivalence_preserves_restrictions {P Q : Karoubi Rec} (f : P ⟶ Q) :
    karoubiEquivalence.functor.map (rst f) =
      rst (karoubiEquivalence.functor.map f) := by
  let := idempotentComplete_v46
  change (toKaroubiEquivalence Object).inverse.map (karoubiInclusion.map (rst f)) =
    rst ((toKaroubiEquivalence Object).inverse.map (karoubiInclusion.map f))
  rw [karoubiInclusion_preserves_restrictions]
  exact V46.equivalence_inverse_preserves (toKaroubiEquivalence Object)
    (fun g => V46.KaroubiRestriction.toKaroubi_preserves g) (karoubiInclusion.map f)

end CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork.Recursion
