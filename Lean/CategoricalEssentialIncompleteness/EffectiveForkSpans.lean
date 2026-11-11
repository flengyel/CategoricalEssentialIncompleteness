/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.EffectiveForkProbes
public import CategoricalEssentialIncompleteness.EffectiveForkTotal

/-! # Total monomorphisms and normalized partial-map spans -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork

open EnumerableCarriers (Carrier val)

theorem total_mono_iff_injective {X Y : Total} (f : X ⟶ Y) :
    Mono f ↔ Injective f.hom := by
  constructor
  · intro hm
    letI : Mono f := hm
    apply injective_of_partialMono
    apply partial_mono_of_total_tests
    intro W u v hu hv he
    let u' : (⟨W⟩ : Total) ⟶ X := ⟨u, hu⟩
    let v' : (⟨W⟩ : Total) ⟶ X := ⟨v, hv⟩
    have he' : u' ≫ f = v' ≫ f := by
      apply WideSubcategory.hom_ext
      exact he
    have huv := (cancel_mono f).mp he'
    exact congrArg (fun k => k.hom ≫ rst f.hom) huv
  · intro hi
    constructor
    intro W u v he
    apply WideSubcategory.hom_ext
    have hh := partialMono_of_injective f.hom hi u.hom v.hom
      (congrArg (fun k => k.hom) he)
    simpa only [show rst f.hom = 𝟙 X.obj from f.property, Category.comp_id] using hh

def domainValue {X Y : Object} (f : X ⟶ Y) : domainObject (Idem.ofRestrict f) ⟶ Y where
  center := EnumerableCarriers.onDomain f.center
  left := EnumerableCarriers.onDomain f.left
  right := EnumerableCarriers.onDomain f.right
  natural_left := by
    intro x y u v hxy hxu hyv
    obtain ⟨_, hu⟩ := (EnumerableCarriers.mem_val_restrictMap _ _ _
      (closed_left (Idem.ofRestrict f)) x u).mp hxu
    exact f.natural_left x y u v hxy hu hyv
  natural_right := by
    intro x y u v hxy hxu hyv
    obtain ⟨_, hu⟩ := (EnumerableCarriers.mem_val_restrictMap _ _ _
      (closed_right (Idem.ofRestrict f)) x u).mp hxu
    exact f.natural_right x y u v hxy hu hyv

theorem domainValue_total {X Y : Object} (f : X ⟶ Y) : isTotal (domainValue f) :=
  (total_iff _).mpr ⟨EnumerableCarriers.onDomain_total f.center,
    EnumerableCarriers.onDomain_total f.left, EnumerableCarriers.onDomain_total f.right⟩

theorem domain_factorization {X Y : Object} (f : X ⟶ Y) :
    domainRetraction (Idem.ofRestrict f) ≫ domainValue f = f := by
  apply Hom.ext
  all_goals apply EnumerableCarriers.val_injective
  · change val (rst f.center ≫ f.center) = val f.center
    rw [rst_comp_self]
  · change val (rst f.left ≫ f.left) = val f.left
    rw [rst_comp_self]
  · change val (rst f.right ≫ f.right) = val f.right
    rw [rst_comp_self]

theorem injective_idem {X : Carrier} (a : Idem X) (x x' y : ℕ)
    (h : y ∈ val a.hom x) (h' : y ∈ val a.hom x') : x=x' := by
  exact ((EnumerableCarriers.mem_val_idem a x y).mp h).2.symm.trans
    ((EnumerableCarriers.mem_val_idem a x' y).mp h').2

theorem domainInclusion_injective {X : Object} (a : Idem X) : Injective (domainInclusion a) :=
  ⟨injective_idem (centerIdem a), injective_idem (leftIdem a), injective_idem (rightIdem a)⟩

def domainInclusionTotal {X : Object} (a : Idem X) :
    (⟨domainObject a⟩ : Total) ⟶ ⟨X⟩ := ⟨domainInclusion a, domainInclusion_total a⟩

instance {X : Object} (a : Idem X) : Mono (domainInclusionTotal a) :=
  (total_mono_iff_injective _).mpr (domainInclusion_injective a)

/-- Every partial map has a representing span with total monic domain leg. -/
theorem normalized_span {X Y : Object} (f : X ⟶ Y) :
    ∃ (D : Total) (m : D ⟶ (⟨X⟩ : Total)) (v : D ⟶ (⟨Y⟩ : Total)) (r : X ⟶ D.obj),
      Mono m ∧ m.hom ≫ r = 𝟙 D.obj ∧ r ≫ m.hom = rst f ∧ r ≫ v.hom = f :=
  ⟨⟨domainObject (Idem.ofRestrict f)⟩, domainInclusionTotal (Idem.ofRestrict f),
    ⟨domainValue f, domainValue_total f⟩, domainRetraction (Idem.ofRestrict f),
    inferInstance, inclusion_retraction _, retraction_inclusion _, domain_factorization f⟩

end CategoricalEssentialIncompleteness.LocalConnectedness.EffectiveFork
