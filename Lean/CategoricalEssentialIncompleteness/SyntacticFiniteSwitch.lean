/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.SyntacticFamily
import CategoricalEssentialIncompleteness.FiniteSwitch
import CategoricalEssentialIncompleteness.DisjointJoins

/-! # Lemma 6.5: the specified switch in the syntactic category -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open Encodable CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition FailureOfComposition.TypedProgramCategory
open FailureOfComposition.CodedObjectMembership FailureOfComposition.ConcreteEvaluator
open FailureOfComposition.ProgramGraph

namespace CategoricalEssentialIncompleteness.LocalConnectedness.SyntacticModel

attribute [local irreducible] FFL.FirstOrder.Arithmetic.code
  FiniteSwitch.switchCode FiniteSwitch.branchCode

open PartialFunctions

def zeroDomainProgram (q : ℕ) : PCode :=
  .comp .zero (Denumerable.ofNat PCode q)

theorem zeroDomainProgram_spec {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q : ℕ) (x : M) :
    Computes (zeroDomainProgram q) x 0 ↔
      ∃ y : M, (eventualGraph q).val.Evalb ![x, y] := by
  rw [zeroDomainProgram, computes_comp]
  simp_rw [computes_zero]
  simp only [true_and, and_true, Computes, Denumerable.encode_ofNat]

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

theorem domainProgram_support {X : CodedProgramCategory T} (c : Idem X) (q : ℕ)
    (hq : c.hom = arrowOfIndex T (objectCode X) (objectCode X) q)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (x : carrier M (objectCode X)) :
    Computes (zeroDomainProgram (normalizeIndex (objectCode X) (objectCode X) q)) x.val 0 ↔
      x ∈ support ((rangeFunctor T M).mapIdem c) := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  rw [zeroDomainProgram_spec, mem_support]
  change (∃ y : M, (eventualGraph (normalizeIndex _ _ q)).val.Evalb ![x.val, y]) ↔
    ∃ y : carrier M (objectCode X), y ∈ (functor T M).map c.hom x
  rw [hq]
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨_, hq, ht⟩ := (eventualGraph_normalizeIndex_eval _ _ q x.val y).mp hy
    exact ⟨⟨y, ht⟩, (mem_map_index T M _ _ q x ⟨y, ht⟩).mpr hq⟩
  · rintro ⟨y, hy⟩
    exact ⟨y.val, (eventualGraph_normalizeIndex_eval _ _ q x.val y.val).mpr
      ⟨x.property, (mem_map_index T M _ _ q x y).mp hy, y.property⟩⟩

def finiteSwitchArrow (X : CodedProgramCategory T) (q r : ℕ) : X ⟶ coprod X X :=
  arrowOfIndex T (objectCode X) (.coproduct (objectCode X) (objectCode X))
    (encode (FiniteSwitch.switchCode
      (zeroDomainProgram (normalizeIndex (objectCode X) (objectCode X) q))
      (zeroDomainProgram (normalizeIndex (objectCode X) (objectCode X) r))))

theorem mem_finiteSwitchArrow {X : CodedProgramCategory T} (c c' : Idem X)
    (hc : Complementary c c') (q r : ℕ)
    (hq : c.hom = arrowOfIndex T (objectCode X) (objectCode X) q)
    (hr : c'.hom = arrowOfIndex T (objectCode X) (objectCode X) r)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
    [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
    (x : carrier M (objectCode X)) (y : carrier M (.coproduct (objectCode X) (objectCode X))) :
    y ∈ (functor T M).map (finiteSwitchArrow T X q r) x ↔
      (x ∈ support ((rangeFunctor T M).mapIdem c) ∧ y.val = pair x.val 1) ∨
        (x ∈ support ((rangeFunctor T M).mapIdem c') ∧ y.val = pair x.val 0) := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  let : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  let : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₁) inferInstance
  have hd : ¬(Computes (zeroDomainProgram (normalizeIndex (objectCode X) (objectCode X) q)) x.val 0 ∧
      Computes (zeroDomainProgram (normalizeIndex (objectCode X) (objectCode X) r)) x.val 0) := by
    rw [domainProgram_support T c q hq M x, domainProgram_support T c' r hr M x]
    intro h
    have he := congrArg support ((rangeFunctor T M).map_complementary hc).disjoint
    rw [support_inf, support_bot] at he
    exact (show x ∈ (∅ : Set _) from he ▸ h)
  change y ∈ (functor T M).map (arrowOfIndex T _ _ _) x ↔ _
  rw [mem_map_index]
  change Computes (FiniteSwitch.switchCode
    (zeroDomainProgram (normalizeIndex (objectCode X) (objectCode X) q))
    (zeroDomainProgram (normalizeIndex (objectCode X) (objectCode X) r))) x.val y.val ↔ _
  rw [FiniteSwitch.switchCode_graph _ _ _ _ hd,
    domainProgram_support T c q hq M x, domainProgram_support T c' r hr M x]

theorem mapped_support_disjoint {X : CodedProgramCategory T} (c c' : Idem X)
    (hc : Complementary c c') (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] :
    Disjoint (support ((rangeFunctor T M).mapIdem c))
      (support ((rangeFunctor T M).mapIdem c')) := by
  rw [Set.disjoint_iff_inter_eq_empty, ← support_inf,
    ((rangeFunctor T M).map_complementary hc).disjoint, support_bot]

theorem mapped_support_cover {X : CodedProgramCategory T} (c c' : Idem X)
    (hc : Complementary c c') (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] :
    support ((rangeFunctor T M).mapIdem c) ∪
      support ((rangeFunctor T M).mapIdem c') = Set.univ := by
  rw [← support_sup, ((rangeFunctor T M).map_complementary hc).cover, support_top]

theorem finiteSwitchArrow_total {X : CodedProgramCategory T} (c c' : Idem X)
    (hc : Complementary c c') (q r : ℕ)
    (hq : c.hom = arrowOfIndex T (objectCode X) (objectCode X) q)
    (hr : c'.hom = arrowOfIndex T (objectCode X) (objectCode X) r) :
    isTotal (finiteSwitchArrow T X q r) := by
  change rst (finiteSwitchArrow T X q r) = 𝟙 X
  apply joint_faithful T
  intro M _ _
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  let : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  let : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₁) inferInstance
  rw [map_restriction, (functor T M).map_id]
  apply PFun.ext
  intro x y
  rw [mem_rst, mem_id]
  refine ⟨And.right, fun hy => ⟨?_, hy⟩⟩
  have hx : x ∈ support ((rangeFunctor T M).mapIdem c) ∪
      support ((rangeFunctor T M).mapIdem c') := by
    rw [mapped_support_cover T c c' hc M]; trivial
  rcases hx with hx | hx
  · exact ⟨sumCoding T M _ _ (Sum.inr x),
      (mem_finiteSwitchArrow T c c' hc q r hq hr M x _).mpr (Or.inl ⟨hx, rfl⟩)⟩
  · exact ⟨sumCoding T M _ _ (Sum.inl x),
      (mem_finiteSwitchArrow T c c' hc q r hq hr M x _).mpr (Or.inr ⟨hx, rfl⟩)⟩

theorem mem_coded_i0 {X : CodedProgramCategory T}
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
    [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
    (x : carrier M (objectCode X)) (y : carrier M (.coproduct (objectCode X) (objectCode X))) :
    y ∈ (functor T M).map (i0 X X) x ↔ y.val = pair x.val 0 := by
  change y ∈ (functor T M).map (arrowOfIndex T _ _ (TypedCoproducts.leftInjectionIndex _)) x ↔ _
  rw [mem_map_index, TypedCoproducts.eventualGraph_leftInjectionIndex_eval]
  exact and_iff_right x.property

theorem mem_coded_i1 {X : CodedProgramCategory T}
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]
    [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
    (x : carrier M (objectCode X)) (y : carrier M (.coproduct (objectCode X) (objectCode X))) :
    y ∈ (functor T M).map (i1 X X) x ↔ y.val = pair x.val 1 := by
  change y ∈ (functor T M).map (arrowOfIndex T _ _ (TypedCoproducts.rightInjectionIndex _)) x ↔ _
  rw [mem_map_index, TypedCoproducts.eventualGraph_rightInjectionIndex_eval]
  exact and_iff_right x.property

theorem finiteSwitchArrow_branch1 {X : CodedProgramCategory T} (c c' : Idem X)
    (hc : Complementary c c') (q r : ℕ)
    (hq : c.hom = arrowOfIndex T (objectCode X) (objectCode X) q)
    (hr : c'.hom = arrowOfIndex T (objectCode X) (objectCode X) r) :
    c.hom ≫ finiteSwitchArrow T X q r = c.hom ≫ i1 X X := by
  apply joint_faithful T
  intro M _ _
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  let : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  let : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₁) inferInstance
  rw [(functor T M).map_comp, (functor T M).map_comp]
  apply PFun.ext
  intro x y
  rw [mem_comp, mem_comp]
  constructor
  · rintro ⟨w, hw, hy⟩
    obtain ⟨hx, he⟩ := (mem_idem ((rangeFunctor T M).mapIdem c) x w).mp hw
    subst w
    refine ⟨x, hw, (mem_coded_i1 T M x y).mpr ?_⟩
    rcases (mem_finiteSwitchArrow T c c' hc q r hq hr M x y).mp hy with h | h
    · exact h.2
    · exact False.elim (Set.disjoint_left.mp (mapped_support_disjoint T c c' hc M) hx h.1)
  · rintro ⟨w, hw, hy⟩
    obtain ⟨hx, he⟩ := (mem_idem ((rangeFunctor T M).mapIdem c) x w).mp hw
    subst w
    exact ⟨x, hw, (mem_finiteSwitchArrow T c c' hc q r hq hr M x y).mpr
      (Or.inl ⟨hx, (mem_coded_i1 T M x y).mp hy⟩)⟩

theorem finiteSwitchArrow_branch0 {X : CodedProgramCategory T} (c c' : Idem X)
    (hc : Complementary c c') (q r : ℕ)
    (hq : c.hom = arrowOfIndex T (objectCode X) (objectCode X) q)
    (hr : c'.hom = arrowOfIndex T (objectCode X) (objectCode X) r) :
    c'.hom ≫ finiteSwitchArrow T X q r = c'.hom ≫ i0 X X := by
  apply joint_faithful T
  intro M _ _
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  let : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  let : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₁) inferInstance
  rw [(functor T M).map_comp, (functor T M).map_comp]
  apply PFun.ext
  intro x y
  rw [mem_comp, mem_comp]
  constructor
  · rintro ⟨w, hw, hy⟩
    obtain ⟨hx, he⟩ := (mem_idem ((rangeFunctor T M).mapIdem c') x w).mp hw
    subst w
    refine ⟨x, hw, (mem_coded_i0 T M x y).mpr ?_⟩
    rcases (mem_finiteSwitchArrow T c c' hc q r hq hr M x y).mp hy with h | h
    · exact False.elim (Set.disjoint_left.mp (mapped_support_disjoint T c c' hc M) h.1 hx)
    · exact h.2
  · rintro ⟨w, hw, hy⟩
    obtain ⟨hx, he⟩ := (mem_idem ((rangeFunctor T M).mapIdem c') x w).mp hw
    subst w
    exact ⟨x, hw, (mem_finiteSwitchArrow T c c' hc q r hq hr M x y).mpr
      (Or.inr ⟨hx, (mem_coded_i0 T M x y).mp hy⟩)⟩

/-- Lemma 6.5, constructed by the increasing-bound, two-test program. -/
theorem syntactic_finite_switch {X : CodedProgramCategory T} (c c' : Idem X)
    (hc : Complementary c c') :
    ∃ s : X ⟶ coprod X X, isTotal s ∧
      c.hom ≫ s = c.hom ≫ i1 X X ∧ c'.hom ≫ s = c'.hom ≫ i0 X X := by
  obtain ⟨q, hq⟩ := exists_arrowOfIndex T (objectCode X) (objectCode X) c.hom
  obtain ⟨r, hr⟩ := exists_arrowOfIndex T (objectCode X) (objectCode X) c'.hom
  exact ⟨finiteSwitchArrow T X q r, finiteSwitchArrow_total T c c' hc q r hq.symm hr.symm,
    finiteSwitchArrow_branch1 T c c' hc q r hq.symm hr.symm,
    finiteSwitchArrow_branch0 T c c' hc q r hq.symm hr.symm⟩

/-- The same finite program supplies the unique section at every coordinate. -/
theorem family_finite_switch {X : CodedProgramCategory T} (c c' : Idem X)
    (hc : Complementary c c') :
    ∃ s : X ⟶ coprod X X, isTotal s ∧
      c.hom ≫ s = c.hom ≫ i1 X X ∧ c'.hom ≫ s = c'.hom ≫ i0 X X ∧
      (familyFunctor T).map s =
        switchSection ((familyRangeFunctor T).mapIdem c) ((familyRangeFunctor T).mapIdem c')
          ((familyRangeFunctor T).map_complementary hc) ≫
            ((familyRangeFunctor T).comparison X X).hom := by
  obtain ⟨s, ht, h1, h0⟩ := syntactic_finite_switch T c c' hc
  exact ⟨s, ht, h1, h0, image_switch_eq (familyRangeFunctor T) c c' hc s h1 h0⟩

theorem section_lifting_finite_switch (X : CodedProgramCategory T) :
    SectionLifting (familyRangeFunctor T) X := by
  intro c c' hc
  obtain ⟨s, _, _, _, hs⟩ := family_finite_switch T c c' hc
  exact ⟨s, hs⟩

/-- Corollary 6.6 through the specified switch and the source Turing morphism. -/
theorem finite_switch_categorical_pair (hT : Consistent T) :
    Inseparable (syntacticPair0 T) (syntacticPair1 T) :=
  range_functor_lifting (familyRangeFunctor T)
    (FailureOfComposition.TypedTuringMorphism.typedTau T)
    (FailureOfComposition.TypedTuringMorphism.typedTau_isTuringMorphism T)
    (FailureOfComposition.TypedRecursionCategory.omegaCoprodIso T).symm
    (family_nonzero T hT) (section_lifting_finite_switch T _)

end CategoricalEssentialIncompleteness.LocalConnectedness.SyntacticModel
