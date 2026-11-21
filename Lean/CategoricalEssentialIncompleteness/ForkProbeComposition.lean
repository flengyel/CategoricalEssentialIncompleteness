/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ForkProbeFunctor

/-! # Partial postcomposition and the probe domain equation -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork

open EnumerableCarriers (Carrier val Element)

theorem constant_comp_iff {X Y : Carrier} (f : X ⟶ Y) (x : Element X) (y : Element Y) :
    (constant x.val x.property : singletonCarrier ⟶ X) ≫ f=
      constant y.val y.property ↔ y.val ∈ val f x.val := by
  constructor
  · intro h
    have he := congrArg (fun g : singletonCarrier ⟶ Y => val g 0) h
    rw [EnumerableCarriers.val_comp,val_constant_at _ _ _ (by rfl),Part.bind_some,
      val_constant_at _ _ _ (by rfl)] at he
    exact Part.eq_some_iff.mp he
  · intro h
    apply EnumerableCarriers.val_ext_on_source
    intro n hn
    rw [EnumerableCarriers.val_comp,val_constant_at _ _ _ hn,Part.bind_some,
      val_constant_at _ _ _ hn]
    exact Part.eq_some_iff.mpr h

theorem probePoint_comp_iff (i : Bool) {X Y : Object} (f : X ⟶ Y)
    (x : Element ((evaluation (endpoint i)).obj X))
    (y : Element ((evaluation (endpoint i)).obj Y)) :
    (probePoint i x).val ≫ f=(probePoint i y).val ↔
      y.val ∈ val ((evaluation (endpoint i)).map f) x.val := by
  cases i
  · constructor
    · intro h
      exact (constant_comp_iff f.left x y).mp (congrArg Hom.left h)
    · intro h
      exact Hom.ext (CategoryTheory.Limits.zero_comp)
        ((constant_comp_iff f.left x y).mpr h) (CategoryTheory.Limits.zero_comp)
  · constructor
    · intro h
      exact (constant_comp_iff f.right x y).mp (congrArg Hom.right h)
    · intro h
      exact Hom.ext (CategoryTheory.Limits.zero_comp) (CategoryTheory.Limits.zero_comp)
        ((constant_comp_iff f.right x y).mpr h)

/-- The transported functor is literally partial postcomposition on total probe morphisms.
This equation includes its precise definedness. -/
theorem probe_postcomposition (i : Bool) {X Y : Object} (f : X ⟶ Y)
    (p : ProbeTotal i X) (q : ProbeTotal i Y) :
    q ∈ (probeFunctor i).map f p ↔ p.val ≫ f=q.val := by
  rw [mem_probeFunctor]
  have hp := congrArg Subtype.val (probePoint_value i p)
  have hq := congrArg Subtype.val (probePoint_value i q)
  rw [← hp,← hq]
  exact (probePoint_comp_iff i f (probeValue i p) (probeValue i q)).symm

theorem probe_postcomposition_domain (i : Bool) {X Y : Object} (f : X ⟶ Y)
    (p : ProbeTotal i X) : ((probeFunctor i).map f p).Dom ↔ isTotal (p.val ≫ f) := by
  rw [Part.dom_iff_mem]
  constructor
  · rintro ⟨q,hq⟩
    exact (probe_postcomposition i f p q).mp hq ▸ q.property
  · intro ht
    exact ⟨⟨p.val ≫ f,ht⟩,(probe_postcomposition i f p ⟨p.val ≫ f,ht⟩).mpr rfl⟩

theorem singleton_partial_total_or_zero {X : Carrier} (f : singletonCarrier ⟶ X) :
    isTotal f ∨ f=0 := by
  by_cases h : (val f 0).Dom
  · left
    apply (EnumerableCarriers.total_iff f).mpr
    intro n hn
    have he : n=0 := Set.mem_singleton_iff.mp hn
    simpa only [he] using h
  · right
    apply EnumerableCarriers.val_ext_on_source
    intro n hn
    have he : n=0 := Set.mem_singleton_iff.mp hn
    subst n
    exact Part.eq_none_iff'.mpr h

theorem probe_partial_total_or_zero (i : Bool) {Y : Object} (f : endpointProbe i ⟶ Y) :
    isTotal f ∨ f=0 := by
  cases i
  · rcases singleton_partial_total_or_zero f.left with ht|hz
    · exact Or.inl ((total_iff f).mpr ⟨by
        rw [empty_arrow_zero f.center]; exact zero_empty_total _,ht,by
        rw [empty_arrow_zero f.right]; exact zero_empty_total _⟩)
    · exact Or.inr (Hom.ext (empty_arrow_zero f.center) hz (empty_arrow_zero f.right))
  · rcases singleton_partial_total_or_zero f.right with ht|hz
    · exact Or.inl ((total_iff f).mpr ⟨by
        rw [empty_arrow_zero f.center]; exact zero_empty_total _,by
        rw [empty_arrow_zero f.left]; exact zero_empty_total _,ht⟩)
    · exact Or.inr (Hom.ext (empty_arrow_zero f.center) (empty_arrow_zero f.left) hz)

theorem probe_domain (i : Bool) {Y : Object} (e : Idem Y)
    (y : Element ((evaluation (endpoint i)).obj Y)) :
    (probePoint i y).val ≫ e.hom=(probePoint i y).val ↔
      y.val ∈ EnumerableCarriers.support ((evaluationRangeFunctor (endpoint i)).mapIdem e) := by
  rw [probePoint_comp_iff]
  change y.val ∈ val ((evaluationRangeFunctor (endpoint i)).mapIdem e).hom y.val ↔ _
  rw [EnumerableCarriers.mem_val_idem]
  exact and_iff_left rfl

theorem probe_domain_fixed_point (i : Bool) {Y : Object} (e : Idem Y)
    (y : Element ((evaluation (endpoint i)).obj Y)) :
    (probePoint i y).val ≫ e.hom=(probePoint i y).val ↔
      val ((evaluation (endpoint i)).map e.hom) y.val=Part.some y.val :=
  (probePoint_comp_iff i e.hom y y).trans Part.eq_some_iff.symm

end CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork
