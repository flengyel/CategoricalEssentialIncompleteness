/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46DiagramDecidableVariables
public import CategoricalEssentialIncompleteness.V46CategoricalListLaws
public import CategoricalEssentialIncompleteness.V46NumericalForkPartialMaps
import CategoricalEssentialIncompleteness.ForkProbeObservations
import CategoricalEssentialIncompleteness.EffectiveForkUniversal

/-! # The diagonal of the universal fork

The two centre elements in the proof of Proposition B.10 have the same value
at the left endpoint. Precomposition with the left probe distinguishes every
pair of morphisms from the centre probe into the constant Boolean diagram.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.LocalConnectedness
open EffectiveFork

namespace CategoricalEssentialIncompleteness.V46.ForkDiagonalObstruction

private abbrev centerProbe : EffectiveFork.Total := ⟨EffectiveFork.H0⟩
private abbrev leftProbe : EffectiveFork.Total := ⟨EffectiveFork.H1⟩

private def leftInclusion : leftProbe ⟶ centerProbe :=
  ⟨point1 0 (by rfl), point1_total 0 (by rfl)⟩

private theorem leftInclusion_left : leftInclusion.hom.left = 𝟙 singletonCarrier := by
  symm
  apply singleton_arrow_constant
  exact (mem_supportIdentity singletonCarrier.support 0 0).mpr ⟨rfl, rfl⟩

private abbrev constantFunctor : EnumerableCarriers.Total ⥤ EffectiveFork.Total :=
  Functor.const WalkingSpan ⋙ EffectiveFork.totalEquivalence.inverse

private theorem precompose_left_constant (B : EnumerableCarriers.Total)
    {f g : centerProbe ⟶ constantFunctor.obj B} (h : leftInclusion ≫ f = leftInclusion ≫ g) : f = g := by
  have hleft := congrArg (fun p : leftProbe ⟶ constantFunctor.obj B => p.hom.left) h
  change leftInclusion.hom.left ≫ (f.hom.left : singletonCarrier ⟶ B.obj) =
    leftInclusion.hom.left ≫ (g.hom.left : singletonCarrier ⟶ B.obj) at hleft
  rw [leftInclusion_left] at hleft
  have he : f.hom.left = g.hom.left :=
    (Category.id_comp _).symm.trans (hleft.trans (Category.id_comp _))
  have hl (p : centerProbe ⟶ constantFunctor.obj B) : p.hom.left = p.hom.center := by
    have hn := eq_of_respects_total H0.left_total (constantFunctor.obj B).obj.left_total
      ((total_iff _).mp p.property).1 p.hom.natural_left
    change 𝟙 singletonCarrier ≫ p.hom.left = p.hom.center ≫ 𝟙 B.obj at hn
    exact (Category.id_comp _).symm.trans (hn.trans
      (Category.comp_id (p.hom.center : singletonCarrier ⟶ B.obj)))
  have hr (p : centerProbe ⟶ constantFunctor.obj B) : p.hom.right = p.hom.center := by
    have hn := eq_of_respects_total H0.right_total (constantFunctor.obj B).obj.right_total
      ((total_iff _).mp p.property).1 p.hom.natural_right
    change 𝟙 singletonCarrier ≫ p.hom.right = p.hom.center ≫ 𝟙 B.obj at hn
    exact (Category.id_comp _).symm.trans (hn.trans
      (Category.comp_id (p.hom.center : singletonCarrier ⟶ B.obj)))
  have hc := (hl f).symm.trans (he.trans (hl g))
  apply WideSubcategory.hom_ext
  exact EffectiveFork.Hom.ext hc he ((hr f).trans (hc.trans (hr g).symm))

private theorem precompose_left_boolean {f g : centerProbe ⟶ Two EffectiveFork.Total}
    (h : leftInclusion ≫ f = leftInclusion ≫ g) : f = g := by
  let _ : EffectiveFork.totalEquivalence.inverse.IsEquivalence :=
    EffectiveFork.totalEquivalence.symm.isEquivalence_functor
  let e := DiagramDecidableVariables.booleanIso constantFunctor
  apply (cancel_mono e.inv).mp
  apply precompose_left_constant
  simpa only [← Category.assoc] using congrArg (fun p => p ≫ e.inv) h

/-- In any total fork with decidable equality, the left transition distinguishes
centre elements. The centre and left probes realize the two diagonal tests. -/
theorem leftMap_injective_of_decidableVariables {X : EffectiveFork.Total} (E : DecidableVariables X)
    {x y u : ℕ} (hx : u ∈ EnumerableCarriers.val X.obj.leftMap x)
    (hy : u ∈ EnumerableCarriers.val X.obj.leftMap y) : x = y := by
  have sx := EnumerableCarriers.val_source _ _ _ hx
  have sy := EnumerableCarriers.val_source _ _ _ hy
  obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp
    ((EnumerableCarriers.total_iff _).mp X.obj.right_total x sx)
  obtain ⟨w, hw⟩ := Part.dom_iff_mem.mp
    ((EnumerableCarriers.total_iff _).mp X.obj.right_total y sy)
  let p : centerProbe ⟶ X := ⟨point0 x u v sx hx hv, point0_total x u v sx hx hv⟩
  let q : centerProbe ⟶ X := ⟨point0 y u w sy hy hw, point0_total y u w sy hy hw⟩
  have hleft : leftInclusion ≫ p = leftInclusion ≫ q := by
    apply WideSubcategory.hom_ext
    apply EffectiveFork.Hom.ext
    · exact (empty_arrow_zero _).trans (empty_arrow_zero _).symm
    · rfl
    · exact (empty_arrow_zero _).trans (empty_arrow_zero _).symm
  have h : p = q := by
    apply (E.test_true_iff _ _).mp
    apply precompose_left_boolean
    rw [← Category.assoc, prod.comp_lift, Two.comp_constant]
    exact (E.test_true_iff _ _).mpr hleft
  have hc := congrArg (fun f : centerProbe ⟶ X => EnumerableCarriers.val f.hom.center 0) h
  change EnumerableCarriers.val (constant x sx : singletonCarrier ⟶ X.obj.center) 0 =
    EnumerableCarriers.val (constant y sy : singletonCarrier ⟶ X.obj.center) 0 at hc
  rw [val_constant_at _ _ 0 (by rfl), val_constant_at _ _ 0 (by rfl)] at hc
  exact Part.some_injective hc

/-- The universal object of the category of total effective forks admits no
morphism classifying its diagonal as the inverse image of truth. -/
theorem no_decidableVariables_total : ¬ Nonempty (DecidableVariables (⟨EffectiveFork.V⟩ : EffectiveFork.Total)) := by
  rintro ⟨E⟩
  have h (z : ℕ) : Nat.pair 0 0 ∈ EnumerableCarriers.val V.leftMap (quadCode (0,z,0,0)) :=
    (mem_V_left _ _).mpr (left_quad 0 z 0 0).symm
  have eq := leftMap_injective_of_decidableVariables E (h 0) (h 1)
  exact Nat.zero_ne_one (congrArg (fun t : ℕ × ℕ × ℕ × ℕ => t.2.1) (quadCode.injective eq))

/-- Proposition B.10 in the diagram category on the walking span. -/
theorem no_decidableVariables_diagram : ¬ Nonempty (DecidableVariables
    (NumericalTuples.forkEquivalence.functor.obj (⟨EffectiveFork.V⟩ : EffectiveFork.Total))) := by
  rintro ⟨E⟩
  let e := NumericalTuples.forkEquivalence
  let _ : e.inverse.IsEquivalence := e.symm.isEquivalence_functor
  exact no_decidableVariables_total ⟨DiagramDecidableVariables.mapped e.inverse E _
    (e.unitIso.app (⟨EffectiveFork.V⟩ : EffectiveFork.Total)).symm⟩

end CategoricalEssentialIncompleteness.V46.ForkDiagonalObstruction
