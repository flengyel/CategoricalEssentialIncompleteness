/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.SyntacticFiniteSwitch

/-! # Target separators and failure of target Turing universality -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness

namespace PartialFunctionFamilies

open PartialFunctions
universe w
variable {I : Type w}

def complement {X : Family I} (a : Idem X) : Idem X :=
  assemble (fun i => PartialFunctions.setIdem (PartialFunctions.support (component a i))ᶜ)

theorem complement_spec {X : Family I} (a : Idem X) : Complementary a (complement a) := by
  constructor
  · apply component_ext
    intro i
    rw [component_inf,component_bot]
    apply PartialFunctions.support_injective
    simp [complement,PartialFunctions.support_inf]
  · apply component_ext
    intro i
    rw [component_sup,component_top]
    apply PartialFunctions.support_injective
    simp [complement,PartialFunctions.support_sup]

theorem disjoint_le_complement {X : Family I} (a b : Idem X) (h : a ⊓ b=⊥) :
    b ≤ complement a := by
  apply (le_iff_component _ _).mpr
  intro i
  apply (PartialFunctions.le_iff_support _ _).mpr
  have he := congrArg (fun d => PartialFunctions.support (component d i)) h
  rw [component_inf,component_bot,PartialFunctions.support_inf,PartialFunctions.support_bot] at he
  intro x hx
  change x ∉ PartialFunctions.support (component a i)
  intro ha
  have hm : x ∈ PartialFunctions.support (component a i) ∩ PartialFunctions.support (component b i) := ⟨ha,hx⟩
  rw [he] at hm
  exact hm

theorem disjoint_pair_separated {X : Family I} (a b : Idem X) (h : a ⊓ b=⊥) :
    ¬ Inseparable a b := by
  intro hi
  exact hi.no_separator ⟨a,complement a,complement_spec a,le_rfl,disjoint_le_complement a b h⟩

@[implicit_reducible] def numericFamily (I : Type w) : Family I := fun _ => PartialFun.of ℕ
@[implicit_reducible] def numericProductFamily (I : Type w) : Family I := fun _ => PartialFun.of (ℕ × ℕ)

/-- Families of all partial functions admit no universal evaluator with
total parameter maps, as required by Turing universality. -/
theorem no_numeric_family_universal [Nonempty I]
    (tau : numericProductFamily I ⟶ numericFamily I) :
    ¬ (∀ f : numericProductFamily I ⟶ numericFamily I,
      ∃ r : numericFamily I ⟶ numericFamily I,isTotal r ∧
        ∀ (i : I) (z x : ℕ),f i (z,x)=(r i z).bind (fun q => tau i (q,x))) := by
  classical
  intro h
  let f : numericProductFamily I ⟶ numericFamily I :=
    fun i (p : ℕ × ℕ) => if (tau i (p.2,p.2)).Dom then Part.none else Part.some (0 : ℕ)
  obtain ⟨r,hr,he⟩ := h f
  let i : I := Classical.choice ‹Nonempty I›
  have hi := congrFun (congrFun (show rst r=𝟙 (numericFamily I) from hr) i) (0 : ℕ)
  change rst (C := Pfn) (r i) (0 : ℕ)=Part.some (0 : ℕ) at hi
  have hm : (0 : ℕ) ∈ rst (C := Pfn) (r i) (0 : ℕ) := hi.symm ▸ Part.mem_some (0 : ℕ)
  obtain ⟨q,hq⟩ := ((mem_rst (r i) (0 : ℕ) (0 : ℕ)).mp hm).1
  have hd := he i 0 q
  rw [Part.eq_some_iff.mpr hq,Part.bind_some] at hd
  change (if (tau i (q,q)).Dom then Part.none else Part.some (0 : ℕ))=tau i (q,q) at hd
  by_cases ht : (tau i (q,q)).Dom
  · rw [if_pos ht] at hd
    exact (Part.eq_none_iff'.mp hd.symm) ht
  · rw [if_neg ht] at hd
    exact ht (hd ▸ Part.some_dom (0 : ℕ))

end PartialFunctionFamilies

namespace SyntacticModel

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.TypedProgramCategory FailureOfComposition.TypedTuringMorphism
open PartialFunctionFamilies

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

theorem family_tau_not_universal (hT : Consistent T) :
    ¬ (∀ f : numericProductFamily (ModelIndex T) ⟶ numericFamily (ModelIndex T),
      ∃ r : numericFamily (ModelIndex T) ⟶ numericFamily (ModelIndex T),isTotal r ∧
        ∀ (i : ModelIndex T) (z x : ℕ),f i (z,x)=(r i z).bind
          (fun q => (familyFunctor T).map (typedTau T) i (q,x))) := by
  letI := modelIndex_nonempty T hT
  exact no_numeric_family_universal ((familyFunctor T).map (typedTau T))

theorem family_disjoint_pair_separated {X : CodedProgramCategory T} (a b : Idem X)
    (h : a ⊓ b=⊥) :
    ¬ Inseparable ((familyRangeFunctor T).mapIdem a) ((familyRangeFunctor T).mapIdem b) := by
  apply disjoint_pair_separated
  rw [← RangeFunctor.map_inf,h,RangeFunctor.map_bot]

theorem family_complement_no_preimage {X : CodedProgramCategory T} (a b : Idem X)
    (hi : Inseparable a b) : ¬ ∃ c : Idem X,
      (familyRangeFunctor T).mapIdem c=complement ((familyRangeFunctor T).mapIdem a) := by
  let F := familyRangeFunctor T
  have hinj : Function.Injective (F.mapIdem (X := X)) := by
    intro c d h
    exact Idem.ext ((familyFunctor T).map_injective (congrArg Idem.hom h))
  rintro ⟨c,hc⟩
  have hcomp : Complementary a c := by
    constructor
    · apply hinj
      rw [F.map_inf,F.map_bot,hc]
      exact (complement_spec (F.mapIdem a)).disjoint
    · apply hinj
      rw [F.map_sup,F.map_top,hc]
      exact (complement_spec (F.mapIdem a)).cover
  have hb : F.mapIdem b ≤ F.mapIdem c := by
    rw [hc]
    apply disjoint_le_complement
    rw [← F.map_inf,hi.disjoint,F.map_bot]
  have hbc : b ≤ c := by
    apply Idem.le_def.mpr
    apply (familyFunctor T).map_injective
    rw [(familyFunctor T).map_comp]
    exact Idem.le_def.mp hb
  exact hi.no_separator ⟨a,c,hcomp,le_rfl,hbc⟩

/-- For the pair actually constructed by the specified finite switch and
Theorem 6.3, this target complement is not an image of any source idempotent. -/
theorem family_pair_complement_no_preimage (hT : Consistent T) :
    ¬ ∃ c : Idem (omegaObject T),
      (familyRangeFunctor T).mapIdem c=
        complement ((familyRangeFunctor T).mapIdem (syntacticPair0 T)) :=
  family_complement_no_preimage T _ _ (finite_switch_categorical_pair T hT)

end SyntacticModel
end CategoricalEssentialIncompleteness.LocalConnectedness
