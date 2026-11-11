/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.SyntacticPreservation
public import Foundation.FirstOrder.Tarski.Skolemization
public import Mathlib.Basic.Denumerable

/-! # Arithmetic models with carrier `ℕ`

The carrier is fixed; its arithmetic operations range over all interpretations.
In particular this index includes nonstandard models and does not require
soundness in the standard model.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment

namespace CategoricalEssentialIncompleteness.LocalConnectedness.SyntacticModel

@[instance_reducible] def oringOfStructure {M : Type} (s : Tarski.Structure ℒₒᵣ M) : ORingStructure M where
  zero := s.func Language.ORing.Func.zero ![]
  one := s.func Language.ORing.Func.one ![]
  add x y := s.func Language.ORing.Func.add ![x, y]
  mul x y := s.func Language.ORing.Func.mul ![x, y]
  lt x y := s.rel Language.ORing.Rel.lt ![x, y]

theorem oringOfStructure_standardModel {M : Type} [s : Tarski.Structure ℒₒᵣ M]
    [Tarski.Structure.Eq ℒₒᵣ M] :
    @Arithmetic.standardModel M (oringOfStructure s) = s := by
  apply Tarski.Structure.ext
  · funext k f v
    cases f <;> change s.func _ _ = s.func _ v
    all_goals congr 1; funext i; fin_cases i <;> rfl
  · funext k r v
    cases r
    · have hv : ![v 0, v 1] = v := by funext i; fin_cases i <;> rfl
      change (v 0 = v 1) = s.rel Language.ORing.Rel.eq v
      rw [← hv]
      exact propext (Tarski.Structure.Eq.eq (L := ℒₒᵣ) (M := M) (v 0) (v 1)).symm
    · change s.rel _ ![v 0, v 1] = s.rel _ v
      congr 1
      funext i; fin_cases i <;> rfl

@[instance_reducible] def transportORing {M : Type} [ORingStructure M] (e : M ≃ ℕ) : ORingStructure ℕ where
  zero := e 0
  one := e 1
  add x y := e (e.symm x + e.symm y)
  mul x y := e (e.symm x * e.symm y)
  lt x y := e.symm x < e.symm y

theorem transportORing_standardModel {M : Type} [ORingStructure M] (e : M ≃ ℕ) :
    @Arithmetic.standardModel ℕ (transportORing e) = Tarski.Structure.ofEquiv e := by
  apply Tarski.Structure.ext
  · funext k f v
    cases f <;> rfl
  · funext k r v
    cases r
    · exact propext e.symm.injective.eq_iff.symm
    · rfl

/-- Downward Löwenheim--Skolem followed by a bijection with `ℕ`.
Only the theory PA is used to show that the countable carrier is infinite. -/
theorem exists_nat_elementary (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] :
    ∃ s : ORingStructure ℕ, ∀ φ : ArithmeticSentence,
      (letI := s; ℕ↓[ℒₒᵣ] ⊧ φ) ↔ M↓[ℒₒᵣ] ⊧ φ := by
  let H := Tarski.Structure.SkolemHull₀ ℒₒᵣ M
  let raw : Tarski.Structure ℒₒᵣ H := inferInstance
  letI : ORingStructure H := oringOfStructure raw
  have hs : Arithmetic.standardModel H = raw := oringOfStructure_standardModel
  have he : @Tarski.Structure.ElementaryEquiv ℒₒᵣ H M inferInstance inferInstance
      (Arithmetic.standardModel H) (Arithmetic.standardModel M) := by
    rw [hs]
    exact inferInstance
  letI : Tarski.Structure ℒₒᵣ H := Arithmetic.standardModel H
  letI : H↓[ℒₒᵣ] ⊧* 𝗣𝗔 := @Tarski.Structure.ElementaryEquiv.modelsTheory
    ℒₒᵣ H M inferInstance inferInstance _ _ he 𝗣𝗔 |>.mpr inferInstance
  letI : Infinite H := Infinite.of_injective (fun n : ℕ => (n : H))
    (fun _ _ h => Arithmetic.nat_cast_inj.mp h)
  letI : Countable H := Tarski.Structure.SkolemHull.countable₀
  let e : H ≃ ℕ := Classical.choice (inferInstance : Nonempty (H ≃ ℕ))
  refine ⟨transportORing e, ?_⟩
  intro φ
  rw [transportORing_standardModel]
  exact (Tarski.Structure.ElementaryEquiv.ofEquiv e).models.symm.trans he.models

/-- The exact model index of the manuscript. -/
def ModelIndex (T : ArithmeticTheory) :=
  {s : ORingStructure ℕ // letI := s; ℕ↓[ℒₒᵣ] ⊧* T}

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

theorem complete_nat_models (φ : ArithmeticSentence)
    (h : ∀ (s : ORingStructure ℕ),
      letI := s; ℕ↓[ℒₒᵣ] ⊧* T → ℕ↓[ℒₒᵣ] ⊧ φ) : T ⊢ φ := by
  apply Arithmetic.complete.{0} T
  intro M _ _
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  obtain ⟨s, he⟩ := exists_nat_elementary M
  letI := s
  have hm : ℕ↓[ℒₒᵣ] ⊧* T := models_theory_iff.mpr fun ψ hψ =>
    (he ψ).mpr (models_of_mem hψ)
  exact (he φ).mp (h s hm)

theorem modelIndex_nonempty (hT : Consistent T) : Nonempty (ModelIndex T) := by
  by_contra hn
  apply (consistent_iff_unprovable_bot.mp hT)
  apply complete_nat_models T ⊥
  intro s hs
  exact False.elim (hn ⟨⟨s, hs⟩⟩)

open CategoryTheory FailureOfComposition.TypedProgramCategory
open FailureOfComposition FailureOfComposition.ConcreteEvaluator FailureOfComposition.ProofSearch

/-- Uniform graph equality is detected by precisely the models on `ℕ`. -/
theorem joint_faithful_nat {Q R : CodedProgramCategory T} (f g : Q ⟶ R)
    (h : ∀ (s : ORingStructure ℕ) (hs : letI := s; ℕ↓[ℒₒᵣ] ⊧* T),
      letI := s; letI := hs; (functor T ℕ).map f = (functor T ℕ).map g) : f = g := by
  obtain ⟨q, rfl⟩ := exists_arrowOfIndex T (objectCode Q) (objectCode R) f
  obtain ⟨r, rfl⟩ := exists_arrowOfIndex T (objectCode Q) (objectCode R) g
  apply (arrowOfIndex_eq_iff_eqIndex_normalize T _ _ q r).mpr
  apply complete_nat_models T
  intro s hs
  letI := s
  letI := hs
  let : ℕ↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro x y
  rw [eventualGraph_normalizeIndex_eval, eventualGraph_normalizeIndex_eval]
  constructor
  · rintro ⟨hx, hq, hy⟩
    have hp := (mem_map_index T ℕ _ _ q ⟨x, hx⟩ ⟨y, hy⟩).mpr hq
    rw [h s hs] at hp
    exact ⟨hx, (mem_map_index T ℕ _ _ r ⟨x, hx⟩ ⟨y, hy⟩).mp hp, hy⟩
  · rintro ⟨hx, hr, hy⟩
    have hp := (mem_map_index T ℕ _ _ r ⟨x, hx⟩ ⟨y, hy⟩).mpr hr
    rw [← h s hs] at hp
    exact ⟨hx, (mem_map_index T ℕ _ _ q ⟨x, hx⟩ ⟨y, hy⟩).mp hp, hy⟩

theorem joint_faithful_recursive_nat {Q R : CodedProgramCategory T} (f g : Q ⟶ R)
    (h : ∀ (s : ORingStructure ℕ) (hs : letI := s; ℕ↓[ℒₒᵣ] ⊧* T),
      letI := s; letI := hs; (modelFunctor T ℕ).map f = (modelFunctor T ℕ).map g) : f = g := by
  apply joint_faithful_nat T f g
  intro s hs
  letI := s
  letI := hs
  apply PFun.ext
  intro x y
  have hm := mem_model T ℕ f ((codingEquiv T ℕ _).symm x) ((codingEquiv T ℕ _).symm y)
  have hn := mem_model T ℕ g ((codingEquiv T ℕ _).symm x) ((codingEquiv T ℕ _).symm y)
  simp only [Equiv.apply_symm_apply] at hm hn
  exact hm.symm.trans ((by rw [h s hs] :
    _ ∈ (modelFunctor T ℕ).map f _ ↔ _ ∈ (modelFunctor T ℕ).map g _).trans hn)

end CategoricalEssentialIncompleteness.LocalConnectedness.SyntacticModel
