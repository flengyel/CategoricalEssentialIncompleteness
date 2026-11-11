/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.RestrictionFunctorEquivalences
public import CategoricalEssentialIncompleteness.EnumerableInseparability

/-! # The observation argument for an arbitrary restriction observation functor -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness

universe u v
variable {C : Type u} [Category.{v} C] [RestrictionCategory C]
  [CategoryTheory.Limits.HasZeroMorphisms C] [RestrictionZero C] [BinaryJoins C]

namespace PreservesRestriction

variable {F : C ⥤ EnumerableCarriers.Carrier} (hF : PreservesRestriction F)

theorem map_inf {X : C} (a b : Idem X) :
    hF.mapIdem (a ⊓ b)=hF.mapIdem a ⊓ hF.mapIdem b := Idem.ext (F.map_comp _ _)

theorem map_pull {X Y : C} (f : X ⟶ Y) (a : Idem Y) :
    hF.mapIdem (Idem.pull f a)=Idem.pull (F.map f) (hF.mapIdem a) := by
  apply Idem.ext
  change F.map (rst (f ≫ a.hom))=rst (F.map f ≫ F.map a.hom)
  rw [hF,F.map_comp]

theorem map_mono {X : C} : Monotone (hF.mapIdem (X := X)) := by
  intro a b h
  apply Idem.le_def.mpr
  change F.map a.hom ≫ F.map b.hom=F.map a.hom
  rw [← F.map_comp,Idem.le_def.mp h]

theorem map_bot (hz : ∀ X Y,F.map (0 : X ⟶ Y)=0) {X : C} :
    hF.mapIdem (⊥ : Idem X)=⊥ := Idem.ext (hz X X)

end PreservesRestriction

/-- Section 8's general observation principle. Its functor preserves exactly
restrictions, zeros and binary idempotent joins. It need not preserve ranges,
products or coproducts, or be faithful. -/
theorem general_observed_incompleteness (F : C ⥤ EnumerableCarriers.Carrier)
    (hF : PreservesRestriction F) (hz : ∀ X Y,F.map (0 : X ⟶ Y)=0)
    (_hj : ∀ {X : C} (a b : Idem X),hF.mapIdem (a ⊔ b)=hF.mapIdem a ⊔ hF.mapIdem b)
    {U S : C} (a b : Idem U)
    (hab : Numerical.RecursivelyInseparable (EnumerableCarriers.support (hF.mapIdem a))
      (EnumerableCarriers.support (hF.mapIdem b)))
    (theta : U ⟶ S) (_htheta : isTotal theta) (nu : S ⟶ S) (_hnu : isTotal nu)
    (t0 : Idem S) (ha : a ≤ Idem.pull theta t0)
    (hb : b ≤ Idem.pull theta (Idem.pull nu t0))
    (t : Idem S) (ht : t0 ≤ t) (hc : t ⊓ Idem.pull nu t=⊥) :
    (REPred (· ∈ EnumerableCarriers.support (hF.mapIdem (Idem.pull theta t))) ∧
      REPred (· ∈ EnumerableCarriers.support (hF.mapIdem (Idem.pull theta (Idem.pull nu t))))) ∧
    Numerical.RecursivelyInseparable
      (EnumerableCarriers.support (hF.mapIdem (Idem.pull theta t)))
      (EnumerableCarriers.support (hF.mapIdem (Idem.pull theta (Idem.pull nu t)))) := by
  have hA := (EnumerableCarriers.support_le_iff _ _).mp
    (hF.map_mono (ha.trans (Idem.pull_mono theta ht)))
  have hB := (EnumerableCarriers.support_le_iff _ _).mp
    (hF.map_mono (hb.trans (Idem.pull_mono theta (Idem.pull_mono nu ht))))
  have hd : hF.mapIdem (Idem.pull theta t) ⊓
      hF.mapIdem (Idem.pull theta (Idem.pull nu t))=⊥ := by
    rw [← hF.map_inf,← Idem.pull_inf,hc,Idem.pull_bot,hF.map_bot hz]
  have hsets : Disjoint (EnumerableCarriers.support (hF.mapIdem (Idem.pull theta t)))
      (EnumerableCarriers.support (hF.mapIdem (Idem.pull theta (Idem.pull nu t)))) := by
    apply Set.disjoint_iff_inter_eq_empty.mpr
    simpa only [EnumerableCarriers.support_inf,EnumerableCarriers.support_bot] using
      congrArg EnumerableCarriers.support hd
  refine ⟨⟨EnumerableCarriers.support_re _,EnumerableCarriers.support_re _⟩,hsets,?_⟩
  rintro ⟨D,hD,hP,hN⟩
  apply hab.2
  refine ⟨D,hD,hA.trans hP,Set.disjoint_left.mpr ?_⟩
  intro n hnD hnB
  exact Set.disjoint_left.mp hN hnD (hB hnB)

end CategoricalEssentialIncompleteness.LocalConnectedness
