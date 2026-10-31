/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.SyntacticFamilyExtension
import CategoricalEssentialIncompleteness.ClassicalProgramCategory
import CategoricalEssentialIncompleteness.ArithmeticCategoricalIncompleteness
import Foundation.FirstOrder.Arithmetic.TA.Basic

/-! # The syntactic category of the full standard theory is classical Rec -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition FailureOfComposition.TypedProgramCategory
open FailureOfComposition.CodedObjectMembership FailureOfComposition.ConcreteEvaluator
open FailureOfComposition.ProofSearch FailureOfComposition.UniformIndexQuotient

namespace CategoricalEssentialIncompleteness.LocalConnectedness.StandardTrueTheory

open SyntacticModel

instance raw_faithful : (functor 𝗧𝗔 ℕ).Faithful where
  map_injective {Q R} f g h := by
    obtain ⟨q,rfl⟩ := exists_arrowOfIndex 𝗧𝗔 (objectCode Q) (objectCode R) f
    obtain ⟨r,rfl⟩ := exists_arrowOfIndex 𝗧𝗔 (objectCode Q) (objectCode R) g
    apply (arrowOfIndex_eq_iff_eqIndex_normalize 𝗧𝗔 _ _ q r).mpr
    apply TA.provable_iff.mpr
    rw [models_iff,uniformSentence_eval]
    intro x y
    rw [eventualGraph_normalizeIndex_eval,eventualGraph_normalizeIndex_eval]
    constructor
    · rintro ⟨hx,hq,hy⟩
      have hp := (mem_map_index 𝗧𝗔 ℕ _ _ q ⟨x,hx⟩ ⟨y,hy⟩).mpr hq
      rw [h] at hp
      exact ⟨hx,(mem_map_index 𝗧𝗔 ℕ _ _ r ⟨x,hx⟩ ⟨y,hy⟩).mp hp,hy⟩
    · rintro ⟨hx,hr,hy⟩
      have hp := (mem_map_index 𝗧𝗔 ℕ _ _ r ⟨x,hx⟩ ⟨y,hy⟩).mpr hr
      rw [← h] at hp
      exact ⟨hx,(mem_map_index 𝗧𝗔 ℕ _ _ q ⟨x,hx⟩ ⟨y,hy⟩).mp hp,hy⟩

instance recursive_faithful : (modelFunctor 𝗧𝗔 ℕ).Faithful where
  map_injective {Q R} f g h := by
    apply (functor 𝗧𝗔 ℕ).map_injective
    apply PFun.ext
    intro x y
    have hm := mem_model 𝗧𝗔 ℕ f ((codingEquiv 𝗧𝗔 ℕ _).symm x) ((codingEquiv 𝗧𝗔 ℕ _).symm y)
    have hn := mem_model 𝗧𝗔 ℕ g ((codingEquiv 𝗧𝗔 ℕ _).symm x) ((codingEquiv 𝗧𝗔 ℕ _).symm y)
    simp only [Equiv.apply_symm_apply] at hm hn
    exact hm.symm.trans ((by rw [h] :
      _ ∈ (modelFunctor 𝗧𝗔 ℕ).map f _ ↔ _ ∈ (modelFunctor 𝗧𝗔 ℕ).map g _).trans hn)

theorem map_index (Q R : STObjectCode) (q : ℕ) :
    (modelFunctor 𝗧𝗔 ℕ).map (arrowOfIndex 𝗧𝗔 Q R q)=
      (modelFunctor 𝗣𝗔 ℕ).map (arrowOfIndex 𝗣𝗔 Q R q) := by
  have h := model_extension_map 𝗣𝗔 𝗧𝗔 (M := ℕ) (arrowOfIndex 𝗣𝗔 Q R q)
  rw [SyntacticExtension.map_index] at h
  exact h

def comparison : CodedProgramCategory 𝗧𝗔 ⥤ ClassicalPrograms.Rec where
  obj Q := ⟨object 𝗣𝗔 (objectCode Q)⟩
  map {Q R} f :=
    ⟨(modelFunctor 𝗧𝗔 ℕ).map f,by
      obtain ⟨q,rfl⟩ := exists_arrowOfIndex 𝗧𝗔 (objectCode Q) (objectCode R) f
      exact ⟨arrowOfIndex 𝗣𝗔 _ _ q,(map_index _ _ q).symm⟩⟩
  map_id Q := FunctorImage.Hom.ext ((modelFunctor 𝗧𝗔 ℕ).map_id Q)
  map_comp f g := FunctorImage.Hom.ext ((modelFunctor 𝗧𝗔 ℕ).map_comp f g)

instance comparison_faithful : comparison.Faithful where
  map_injective h := (modelFunctor 𝗧𝗔 ℕ).map_injective (congrArg FunctorImage.Hom.val h)

instance comparison_full : comparison.Full where
  map_surjective {Q R} f := by
    obtain ⟨g,hg⟩ := f.represented
    obtain ⟨q,rfl⟩ := exists_arrowOfIndex 𝗣𝗔 (objectCode Q) (objectCode R) g
    refine ⟨arrowOfIndex 𝗧𝗔 _ _ q,FunctorImage.Hom.ext ?_⟩
    exact (map_index _ _ q).trans hg

instance comparison_essSurj : comparison.EssSurj where
  mem_essImage X := ⟨object 𝗧𝗔 (objectCode X.base),⟨Iso.refl X⟩⟩

instance comparison_isEquivalence : comparison.IsEquivalence where

def equivalence : CodedProgramCategory 𝗧𝗔 ≌ ClassicalPrograms.Rec := comparison.asEquivalence

theorem complete : Complete 𝗧𝗔 := by
  constructor
  intro φ
  by_cases h : ℕ↓[ℒₒᵣ] ⊧ φ
  · exact Or.inl (TA.provable_iff.mpr h)
  · exact Or.inr (TA.provable_iff.mpr (Semantics.Not.models_not.mpr h))

theorem consistent : Consistent 𝗧𝗔 := by
  apply consistent_iff_unprovable_bot.mpr
  intro h
  have hm := TA.provable_iff.mp h
  simpa [models_iff] using hm

theorem not_enumerable : ¬ 𝗧𝗔.RE := by
  intro h
  letI := h
  letI := complete
  exact not_complete_iff_incomplete.mpr (ArithmeticApplication.arithmetic_incomplete 𝗧𝗔 consistent)
    inferInstance

end CategoricalEssentialIncompleteness.LocalConnectedness.StandardTrueTheory
