/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module
public import CategoricalEssentialIncompleteness.V46ArithmeticDiagonalSplitting
public import CategoricalEssentialIncompleteness.V46ArithmeticSentenceInseparabilityDiagonal
public import Foundation.FirstOrder.Arithmetic.R0.Representation

/-! # Subobject separators of the arithmetic diagonal pair -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists

namespace CategoricalEssentialIncompleteness.V46.ArithmeticSignedSeparator
open ArithmeticSignedAtoms SyntacticSyntax
local notation "N" => (PrintedObjectCoding.Number : PredicateCategory 𝗣𝗔)

def standardSet (A : Subobject (C := PredicateCategory 𝗣𝗔) N) : Set ℕ :=
  {n | (imageCarrier (chosenGraph 𝗣𝗔 A.arrow).graph).val.Evalb ![n]}

theorem mem_standardSet (A : Subobject (C := PredicateCategory 𝗣𝗔) N) (n : ℕ) :
    n ∈ standardSet A ↔ ∃ x : Obj 𝗣𝗔 ℕ (A : PredicateCategory 𝗣𝗔),
      ((F 𝗣𝗔 ℕ).map A.arrow x).val = n := by
  change (imageCarrier _).val.Evalb ![n] ↔ _
  rw [imageCarrier_eval]
  constructor
  · rintro ⟨x, hx⟩
    let xx : Obj 𝗣𝗔 ℕ (A : PredicateCategory 𝗣𝗔) :=
      ⟨x, ((chosenGraph 𝗣𝗔 A.arrow).support_model ℕ x n hx).1⟩
    let nn : Obj 𝗣𝗔 ℕ N := ⟨n, memberFormula_omega_eval n⟩
    exact ⟨xx, congrArg Subtype.val ((chosenGraph_map_iff 𝗣𝗔 ℕ A.arrow xx nn).mp hx)⟩
  · rintro ⟨x, hx⟩
    have h := (chosenGraph_map_iff 𝗣𝗔 ℕ A.arrow x ((F 𝗣𝗔 ℕ).map A.arrow x)).mpr rfl
    rw [hx] at h
    exact ⟨x.val, h⟩

theorem standardSet_re (A : Subobject (C := PredicateCategory 𝗣𝗔) N) :
    REPred (· ∈ standardSet A) := by
  let C := imageCarrier (chosenGraph 𝗣𝗔 A.arrow).graph
  change REPred (fun n : ℕ => C.val.Evalb ![n])
  apply rePred_iff_sigma1.mpr
  refine ⟨C.rew Rew.emb, ?_⟩
  intro v
  simp [← Matrix.fun_eq_vec_one]

theorem standardSet_mono {A B : Subobject (C := PredicateCategory 𝗣𝗔) N} (h : A ≤ B) :
    standardSet A ⊆ standardSet B := by
  intro n hn
  obtain ⟨x, hx⟩ := (mem_standardSet A n).mp hn
  apply (mem_standardSet B n).mpr
  refine ⟨(F 𝗣𝗔 ℕ).map (Subobject.ofLE A B h) x, ?_⟩
  rw [← Functor.map_comp_apply, Subobject.ofLE_arrow]
  exact hx

theorem standardSet_mk {C : PredicateCategory 𝗣𝗔} (m : C ⟶ N) [Mono m] (n : ℕ) :
    n ∈ standardSet (Subobject.mk m) ↔
      ∃ x : Obj 𝗣𝗔 ℕ C, ((F 𝗣𝗔 ℕ).map m x).val = n := by
  rw [mem_standardSet]
  let i := Subobject.underlyingIso m
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨(F 𝗣𝗔 ℕ).map i.hom x, ?_⟩
    have h := ConcreteNamedComparison.parameterPoint_diagram 𝗣𝗔 ℕ i.hom m
      (𝟙 _) (Subobject.mk m).arrow (by simpa only [Category.id_comp] using Subobject.underlyingIso_hom_comp_eq_mk m) x
    simp only [Functor.map_id_apply] at h
    exact (congrArg Subtype.val h).trans hx
  · rintro ⟨x, hx⟩
    refine ⟨(F 𝗣𝗔 ℕ).map i.inv x, ?_⟩
    have h := ConcreteNamedComparison.parameterPoint_diagram 𝗣𝗔 ℕ i.inv (Subobject.mk m).arrow
      (𝟙 _) m (by simpa only [Category.id_comp] using Subobject.underlyingIso_arrow m) x
    simp only [Functor.map_id_apply] at h
    exact (congrArg Subtype.val h).trans hx

theorem positive_set : standardSet positiveSubobject =
    {n : ℕ | ArithmeticDiagonalCodes.alpha.val.Evalb ![n]} := by
  ext n
  rw [positiveSubobject, standardSet_mk]
  simp only [numberInclusion_value]
  exact ⟨fun ⟨x, hx⟩ => hx ▸ x.property, fun hn => ⟨⟨n, hn⟩, rfl⟩⟩

theorem negative_set : standardSet negativeSubobject =
    {n : ℕ | ArithmeticDiagonalCodes.beta.val.Evalb ![n]} := by
  ext n
  rw [negativeSubobject, standardSet_mk]
  simp only [numberInclusion_value]
  exact ⟨fun ⟨x, hx⟩ => hx ▸ x.property, fun hn => ⟨⟨n, hn⟩, rfl⟩⟩

/-- Complementary subobjects have complementary standard numerical images. -/
theorem partition_complement (p : SubobjectPartition (C := PredicateCategory 𝗣𝗔) N) :
    standardSet p.negative = (standardSet p.positive)ᶜ := by
  have cover (n : ℕ) : n ∈ standardSet p.negative ∨ n ∈ standardSet p.positive := by
    let nn : Obj 𝗣𝗔 ℕ N := ⟨n, memberFormula_omega_eval n⟩
    let z := (F 𝗣𝗔 ℕ).map (inv p.cover) nn
    have hz : (F 𝗣𝗔 ℕ).map p.cover z = nn := by
      rw [← Functor.map_comp_apply, IsIso.inv_hom_id, Functor.map_id_apply]
    rcases modelSum_cases 𝗣𝗔 ℕ (p.negative : PredicateCategory 𝗣𝗔)
      (p.positive : PredicateCategory 𝗣𝗔) z with ⟨x, hx⟩ | ⟨x, hx⟩
    · left
      apply (mem_standardSet _ _).mpr
      refine ⟨x, ?_⟩
      rw [← hx, ← Functor.map_comp_apply, SubobjectPartition.cover, coprod.inl_desc] at hz
      exact congrArg Subtype.val hz
    · right
      apply (mem_standardSet _ _).mpr
      refine ⟨x, ?_⟩
      rw [← hx, ← Functor.map_comp_apply, SubobjectPartition.cover, coprod.inr_desc] at hz
      exact congrArg Subtype.val hz
  have disjoint (n : ℕ) : ¬(n ∈ standardSet p.negative ∧ n ∈ standardSet p.positive) := by
    rintro ⟨hn, hp⟩
    obtain ⟨x, hx⟩ := (mem_standardSet _ n).mp hn
    obtain ⟨y, hy⟩ := (mem_standardSet _ n).mp hp
    have he : (F 𝗣𝗔 ℕ).map p.cover ((F 𝗣𝗔 ℕ).map coprod.inl x) =
        (F 𝗣𝗔 ℕ).map p.cover ((F 𝗣𝗔 ℕ).map coprod.inr y) := by
      rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
      simp only [SubobjectPartition.cover, coprod.inl_desc, coprod.inr_desc]
      exact Subtype.ext (hx.trans hy.symm)
    exact modelSum_disjoint 𝗣𝗔 ℕ _ _ x y
      (((F 𝗣𝗔 ℕ).mapIso (asIso p.cover)).toEquiv.injective he)
  ext n
  constructor
  · intro hn hp
    exact disjoint n ⟨hn, hp⟩
  · intro hp
    exact (cover n).resolve_right hp

theorem partition_computable (p : SubobjectPartition (C := PredicateCategory 𝗣𝗔) N) :
    ComputablePred (· ∈ standardSet p.positive) := by
  apply ComputablePred.computable_iff_re_compl_re'.mpr
  refine ⟨standardSet_re _, ?_⟩
  have h : (fun n => n ∈ standardSet p.negative) =
      (fun n => ¬ n ∈ standardSet p.positive) := by
    rw [partition_complement]
    rfl
  rw [← h]
  exact standardSet_re _

/-- A categorical separator would give a recursive separator of the diagonal. -/
theorem no_separator : ¬ HasSubobjectSeparator positiveSubobject negativeSubobject := by
  rintro ⟨p, hp, hn⟩
  apply ArithmeticSentenceInseparability.diagonal_no_recursive_separator
  refine ⟨standardSet p.positive, partition_computable p, ?_, ?_⟩
  · rw [← positive_set]
    exact standardSet_mono hp
  · apply Set.disjoint_left.mpr
    intro n hpos hneg
    have hn' : n ∈ standardSet p.negative := standardSet_mono hn (by rwa [negative_set])
    rw [partition_complement] at hn'
    exact hn' hpos

end CategoricalEssentialIncompleteness.V46.ArithmeticSignedSeparator
