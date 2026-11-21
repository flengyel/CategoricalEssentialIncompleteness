/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.ClassicalRealization
public import CategoricalEssentialIncompleteness.ArithmeticRepresentation

/-! # Arithmetic formulas for the classical diagonal pair -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory CategoryTheory.RestrictionCategory
open CategoryTheory.CoprodStruct CategoryTheory.HasCoproducts
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open FailureOfComposition FailureOfComposition.ConcreteEvaluator
open FailureOfComposition.TypedProgramCategory FailureOfComposition.TypedTuringMorphism
open FailureOfComposition.TypedRecursionCategory

namespace CategoricalEssentialIncompleteness.LocalConnectedness.ClassicalPrograms

open SyntacticModel PartialFunctions

/-- `j = 0` asserts an even output and `j = 1` an odd output of
the fixed Turing morphism on the diagonal. -/
def outputPredicate (j : ℕ) : 𝚺₁.Semisentence 1 :=
  .mkSigma “x. ∃ p y m, !pairDef p x x ∧ !(eventualGraph tauIndex).val p y ∧ y = 2 * m + !!j”

theorem outputPredicate_eval {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (j : ℕ) (x : M) :
    (outputPredicate j).val.Evalb ![x] ↔
      ∃ y m : M, (eventualGraph tauIndex).val.Evalb ![pair x x, y] ∧ y = 2 * m + (j : M) := by
  simp [outputPredicate, numeral_eq_natCast]

theorem outputPredicate_disjoint {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    [M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] (x : M) :
    ¬((outputPredicate 0).val.Evalb ![x] ∧ (outputPredicate 1).val.Evalb ![x]) := by
  rintro ⟨h0, h1⟩
  obtain ⟨y, a, hy, ha⟩ := (outputPredicate_eval 0 x).mp h0
  obtain ⟨z, b, hz, hb⟩ := (outputPredicate_eval 1 x).mp h1
  have he := eventualGraph_output_unique tauIndex (pair x x) y z hy hz
  have hm := congrArg (fun w : M => w % 2) he
  rw [ha, hb] at hm
  simpa using hm

def disjointSentence : ArithmeticSentence :=
  ∀¹ (∼((outputPredicate 0).val ⋏ (outputPredicate 1).val))

theorem pa_proves_output_disjoint : 𝗣𝗔 ⊢ disjointSentence := by
  apply Arithmetic.complete.{0} 𝗣𝗔
  intro M _ _
  let : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  let : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₁) inferInstance
  simpa only [models_iff, disjointSentence, Semiformula.eval_all,
    LogicalConnective.HomClass.map_neg, LogicalConnective.HomClass.map_and,
    LogicalConnective.Prop.neg_eq, LogicalConnective.Prop.and_eq] using
      (outputPredicate_disjoint (M := M))

theorem mem_J_diag (x : ℕ) (y : ℕ × ℕ) :
    y ∈ J.map (PCategoryStruct.diag U) x ↔ y = (x, x) := by
  change y ∈ standardFunctor.map (arrowOfIndex 𝗣𝗔 .omega (.product .omega .omega)
    TypedNearProduct.diagonalIndex) x ↔ _
  rw [mem_model_index, TypedNearProduct.eventualGraph_diagonalIndex_eval]
  change pair y.1 y.2 = pair x x ↔ y = (x, x)
  rw [CodedObjectMembership.pair_eq_pair_iff]
  exact ⟨fun h => Prod.ext h.1 h.2, fun h =>
    ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩

theorem mem_J_tau (x : ℕ × ℕ) (y : ℕ) :
    y ∈ J.map tau x ↔ (eventualGraph tauIndex).val.Evalb ![pair x.1 x.2, y] :=
  mem_model_index 𝗣𝗔 ℕ (.product .omega .omega) .omega tauIndex x y

theorem mem_J_parity_inl (n m : ℕ) :
    Sum.inl m ∈ J.map parityIso.hom n ↔ n = 2 * m := by
  letI : Div ℕ := Arithmetic.instDiv_foundation
  letI : Mod ℕ := Arithmetic.instMod_foundation
  change Sum.inl m ∈ standardFunctor.map
    (arrowOfIndex 𝗣𝗔 .omega (.coproduct .omega .omega) omegaCoprodDecodeIndex) n ↔ _
  rw [mem_model_index, eventualGraph_omegaCoprodDecodeIndex_eval]
  change pair m 0 = pair (n / 2) (n % 2) ↔ n = 2 * m
  rw [CodedObjectMembership.pair_eq_pair_iff]
  constructor
  · rintro ⟨hm, hmod⟩
    have he := Arithmetic.div_add_mod n 2
    simpa only [← hm, ← hmod, add_zero] using he.symm
  · rintro rfl
    simp

theorem mem_J_parity_inr (n m : ℕ) :
    Sum.inr m ∈ J.map parityIso.hom n ↔ n = 2 * m + 1 := by
  letI : Div ℕ := Arithmetic.instDiv_foundation
  letI : Mod ℕ := Arithmetic.instMod_foundation
  change Sum.inr m ∈ standardFunctor.map
    (arrowOfIndex 𝗣𝗔 .omega (.coproduct .omega .omega) omegaCoprodDecodeIndex) n ↔ _
  rw [mem_model_index, eventualGraph_omegaCoprodDecodeIndex_eval]
  change pair m 1 = pair (n / 2) (n % 2) ↔ n = 2 * m + 1
  rw [CodedObjectMembership.pair_eq_pair_iff]
  constructor
  · rintro ⟨hm, hmod⟩
    have he := Arithmetic.div_add_mod n 2
    simpa only [← hm, ← hmod] using he.symm
  · rintro rfl
    simp

theorem J_summand0 : inclusionRangeFunctor.mapIdem (summand0 U U) =
    summand0 (J.obj U) (J.obj U) := Idem.ext rfl

theorem J_summand1 : inclusionRangeFunctor.mapIdem (summand1 U U) =
    summand1 (J.obj U) (J.obj U) := Idem.ext rfl

theorem mem_support_summand0 (z : ℕ ⊕ ℕ) :
    z ∈ support (summand0 (PartialFun.of ℕ) (PartialFun.of ℕ)) ↔
      ∃ n, z = Sum.inl n := by
  rw [mem_support]
  change (∃ w, w ∈ coprod_map (𝟙 (PartialFun.of ℕ)) (0 : PartialFun.of ℕ ⟶ PartialFun.of ℕ) z) ↔ _
  cases z <;> simp

theorem mem_support_summand1 (z : ℕ ⊕ ℕ) :
    z ∈ support (summand1 (PartialFun.of ℕ) (PartialFun.of ℕ)) ↔
      ∃ n, z = Sum.inr n := by
  rw [mem_support]
  change (∃ w, w ∈ coprod_map (0 : PartialFun.of ℕ ⟶ PartialFun.of ℕ) (𝟙 (PartialFun.of ℕ)) z) ↔ _
  cases z <;> simp

theorem mem_J_diagonal_parity (x : ℕ) (z : ℕ ⊕ ℕ) :
    z ∈ J.map (PCategoryStruct.diag U ≫ tau ≫ parityIso.hom) x ↔
      ∃ y, (eventualGraph tauIndex).val.Evalb ![pair x x, y] ∧
        z ∈ J.map parityIso.hom y := by
  rw [J.map_comp, J.map_comp]
  simp only [mem_comp]
  constructor
  · rintro ⟨p, hp, y, hy, hz⟩
    have he := (mem_J_diag x p).mp hp
    subst p
    exact ⟨y, (mem_J_tau (x, x) y).mp hy, hz⟩
  · rintro ⟨y, hy, hz⟩
    exact ⟨(x, x), (mem_J_diag x (x, x)).mpr rfl,
      y, (mem_J_tau (x, x) y).mpr hy, hz⟩

theorem evenDiagonal_support (x : ℕ) :
    x ∈ support (inclusionRangeFunctor.mapIdem evenDiagonal) ↔
      (outputPredicate 0).val.Evalb ![x] := by
  change x ∈ support (inclusionRangeFunctor.mapIdem
    (Idem.pull (PCategoryStruct.diag U ≫ tau ≫ parityIso.hom) (summand0 U U))) ↔ _
  rw [RangeFunctor.map_pull, J_summand0, support_pull]
  change (∃ z : ℕ ⊕ ℕ, z ∈ J.map (PCategoryStruct.diag U ≫ tau ≫ parityIso.hom) x ∧
    z ∈ support (summand0 (PartialFun.of ℕ) (PartialFun.of ℕ))) ↔ _
  rw [outputPredicate_eval]
  constructor
  · rintro ⟨z, hz, hs⟩
    obtain ⟨y, hy, hz⟩ := (mem_J_diagonal_parity x z).mp hz
    obtain ⟨m, hm⟩ := (mem_support_summand0 z).mp hs
    subst z
    exact ⟨y, m, hy, by simpa only [Arithmetic.natCast_nat, add_zero] using (mem_J_parity_inl y m).mp hz⟩
  · rintro ⟨y, m, hy, hm⟩
    exact ⟨Sum.inl m, (mem_J_diagonal_parity x (Sum.inl m)).mpr
      ⟨y, hy, (mem_J_parity_inl y m).mpr (by simpa only [Arithmetic.natCast_nat, add_zero] using hm)⟩,
      (mem_support_summand0 (Sum.inl m)).mpr ⟨m, rfl⟩⟩

theorem oddDiagonal_support (x : ℕ) :
    x ∈ support (inclusionRangeFunctor.mapIdem oddDiagonal) ↔
      (outputPredicate 1).val.Evalb ![x] := by
  change x ∈ support (inclusionRangeFunctor.mapIdem
    (Idem.pull (PCategoryStruct.diag U ≫ tau ≫ parityIso.hom) (summand1 U U))) ↔ _
  rw [RangeFunctor.map_pull, J_summand1, support_pull]
  change (∃ z : ℕ ⊕ ℕ, z ∈ J.map (PCategoryStruct.diag U ≫ tau ≫ parityIso.hom) x ∧
    z ∈ support (summand1 (PartialFun.of ℕ) (PartialFun.of ℕ))) ↔ _
  rw [outputPredicate_eval]
  constructor
  · rintro ⟨z, hz, hs⟩
    obtain ⟨y, hy, hz⟩ := (mem_J_diagonal_parity x z).mp hz
    obtain ⟨m, hm⟩ := (mem_support_summand1 z).mp hs
    subst z
    exact ⟨y, m, hy, by simpa only [Arithmetic.natCast_nat] using (mem_J_parity_inr y m).mp hz⟩
  · rintro ⟨y, m, hy, hm⟩
    exact ⟨Sum.inr m, (mem_J_diagonal_parity x (Sum.inr m)).mpr
      ⟨y, hy, (mem_J_parity_inr y m).mpr (by simpa only [Arithmetic.natCast_nat] using hm)⟩,
      (mem_support_summand1 (Sum.inr m)).mpr ⟨m, rfl⟩⟩

/-- A true finite computation gives a proof of its individual numeral instance. -/
theorem output_numeral_provable (j n : ℕ)
    (h : (outputPredicate j).val.Evalb ![n]) :
    𝗣𝗔 ⊢ ((outputPredicate j).val/[(↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence) := by
  let : 𝗥₀ ⪯ 𝗣𝗔 := WeakerThan.trans (𝓣 := 𝗣𝗔⁻) inferInstance inferInstance
  apply sigma_one_completeness (by simp)
  simpa [models_iff] using h

theorem numeralInstance_eval {M : Type} [ORingStructure M]
    (φ : ArithmeticSemisentence 1) (n : ℕ) :
    M↓[ℒₒᵣ] ⊧ (φ/[(↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence) ↔
      φ.Evalb ![(ORingStructure.numeral n : M)] := by
  simp [models_iff]

/-- The negative numeral proof uses finite computation of the odd output
and PA-provable functionality and parity. No soundness of an extension is used. -/
theorem odd_output_refutes_even (n : ℕ) (h : (outputPredicate 1).val.Evalb ![n]) :
    𝗣𝗔 ⊢ ∼((outputPredicate 0).val/[(↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence) := by
  have hb := output_numeral_provable 1 n h
  apply Arithmetic.complete.{0} 𝗣𝗔
  intro M _ _
  let : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := models_of_subtheory (U := 𝗣𝗔) inferInstance
  let : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := models_of_subtheory (U := 𝗜𝚺₁) inferInstance
  rw [Semantics.Not.models_not, numeralInstance_eval]
  intro ha
  have hbM : M↓[ℒₒᵣ] ⊧
      ((outputPredicate 1).val/[(↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence) :=
    consequence_iff.mp (Theory.Proof.sound hb) M inferInstance
  exact outputPredicate_disjoint _ ⟨ha, (numeralInstance_eval _ n).mp hbM⟩

end CategoricalEssentialIncompleteness.LocalConnectedness.ClassicalPrograms
