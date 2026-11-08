/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46MillerTotalRealization
import CategoricalEssentialIncompleteness.V46PartialMapEquivalence

/-! # Actual monic spans and partial inverses in the total realization

The already proved monic-span comparison is instantiated with the actual
semidecidable carrier presentation. Its splitting and weak-choice
hypotheses were constructed here; none is a new final assumption.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.RestrictionCategory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
namespace CategoricalEssentialIncompleteness.V46.Miller.Total

def partialMapEquivalence (z : Point) :
    PartialMaps.Par (CanonicalTotal z) ≌ SplitObject (Uniform.PointObject z) :=
  (PartialMapEquivalence.equivalence (pointPresentation z).symm).trans
    (carrierEquivalence (P := Uniform.Family.ofPoint z))

theorem partialMap_preserves_restrictions (z : Point)
    {X Y : PartialMaps.Par (CanonicalTotal z)} (f : X ⟶ Y) :
    (partialMapEquivalence z).functor.map (rst f) =
      rst ((partialMapEquivalence z).functor.map f) := by
  change inclusion.map ((PartialMapEquivalence.functor (pointPresentation z).symm).map (rst f)) = _
  rw [PartialMapEquivalence.preserves_restrictions]
  exact inclusion_rst _

theorem partialMap_inverse_preserves_restrictions (z : Point)
    {X Y : SplitObject (Uniform.PointObject z)} (f : X ⟶ Y) :
    (partialMapEquivalence z).inverse.map (rst f) =
      rst ((partialMapEquivalence z).inverse.map f) :=
  LocalConnectedness.V46.equivalence_inverse_preserves (partialMapEquivalence z)
    (partialMap_preserves_restrictions z) f

private theorem conjugate_partial_inverse {C : Type*} [Category C] [RestrictionCategory C]
    {U V X Y : C} (i : U ≅ X) (j : V ≅ Y) (a : U ⟶ V) (b : V ⟶ U) (m : X ⟶ Y)
    (hab : a ≫ b = 𝟙 U) (hba : b ≫ a = rst b)
    (hn : a ≫ j.hom = i.hom ≫ m) :
    ∃ r : Y ⟶ X, m ≫ r = 𝟙 X ∧ r ≫ m = rst r := by
  let r : Y ⟶ X := j.inv ≫ b ≫ i.hom
  have he : m ≫ j.inv = i.inv ≫ a := by
    apply (cancel_epi i.hom).mp
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [← hn]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hm : m ≫ r = 𝟙 X := by
    dsimp [r]
    rw [← Category.assoc m, he]
    calc
      (i.inv ≫ a) ≫ b ≫ i.hom = i.inv ≫ (a ≫ b) ≫ i.hom := by
        simp only [Category.assoc]
      _ = 𝟙 X := by rw [hab, Category.id_comp, i.inv_hom_id]
  have hr : r ≫ m = rst r := by
    calc
      r ≫ m = j.inv ≫ (b ≫ a) ≫ j.hom := by
        dsimp [r]
        simp only [Category.assoc]
        rw [← hn]
      _ = j.inv ≫ rst b ≫ j.hom := by rw [hba]
      _ = (rst (j.inv ≫ b) ≫ j.inv) ≫ j.hom := by
        rw [rst_comp]
        simp only [Category.assoc]
      _ = rst (j.inv ≫ b) := by
        rw [Category.assoc, j.inv_hom_id, Category.comp_id]
      _ = rst r := by
        dsimp [r]
        simpa only [Category.assoc] using
          (rst_comp_of_isTotal (j.inv ≫ b) (iso_total i)).symm
  exact ⟨r, hm, hr⟩

/-- The inverse is an actual arrow in the original restriction splitting,
with the given total mono, rather than a change of its carrier. -/
theorem mono_has_partial_inverse (z : Point) {X Y : CanonicalTotal z}
    (m : X ⟶ Y) [Mono m] :
    ∃ r : Y.obj ⟶ X.obj,m.hom ≫ r = 𝟙 X.obj ∧ r ≫ m.hom = rst r := by
  let E := pointPresentation z
  let n := E.inverse.map m
  have : Mono n := by dsimp [n]; infer_instance
  let s := PartialSpans.inverse n
  let iX := E.counitIso.app X
  let iY := E.counitIso.app Y
  let a := inclusion.map n.hom
  let b := inclusion.map s
  have hab : a ≫ b = 𝟙 _ := by
    change inclusion.map n.hom ≫ inclusion.map s = _
    rw [← inclusion.map_comp,PartialSpans.hom_inverse,inclusion.map_id]
  have hba : b ≫ a = rst b := by
    change inclusion.map s ≫ inclusion.map n.hom = _
    rw [← inclusion.map_comp,PartialSpans.inverse_hom]
    exact inclusion_rst s
  have hn : a ≫ iY.hom.hom = iX.hom.hom ≫ m.hom := by
    exact congrArg (fun k => k.hom) (E.counitIso.hom.naturality m)
  let jX : inclusion.obj (E.inverse.obj X).obj ≅ X.obj :=
    ⟨iX.hom.hom, iX.inv.hom,
      congrArg (fun k => k.hom) iX.hom_inv_id,
      congrArg (fun k => k.hom) iX.inv_hom_id⟩
  let jY : inclusion.obj (E.inverse.obj Y).obj ≅ Y.obj :=
    ⟨iY.hom.hom, iY.inv.hom,
      congrArg (fun k => k.hom) iY.hom_inv_id,
      congrArg (fun k => k.hom) iY.inv_hom_id⟩
  exact conjugate_partial_inverse jX jY a b m.hom hab hba hn

end CategoricalEssentialIncompleteness.V46.Miller.Total
