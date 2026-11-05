/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonBooleans
import CategoricalEssentialIncompleteness.V46ConcreteNamedComparisonLists

/-! # Numerical membership is the actual parameterized Boolean list fold -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoryTheory.Limits
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates
open CategoricalEssentialIncompleteness.V46.SyntacticLists

namespace CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (V : PredicateCategory T)

theorem membership_step_reassociate
    (f : V ⨯ listObject T V ⟶ Two (PredicateCategory T)) :
    (lists T V).parameterRec f ≫
      StableListAlgebra.membershipStep (SyntacticDecidableVariables.decidableVariables T V) =
        Two.binary Bool.or
          (prod.lift prod.fst (prod.snd ≫ prod.fst) ≫ SyntacticDecidableVariables.test T V)
          (prod.lift prod.fst (prod.snd ≫ prod.snd) ≫ f) := by
  simp [StableListAlgebra.parameterRec,StableListAlgebra.membershipStep,
    Two.comp_binary,prod.comp_lift_assoc,SyntacticDecidableVariables.decidableVariables]
  rfl

theorem membershipArrow_nil :
    (lists T V).parameterNil V ≫ membershipArrow T V = Two.constant V false := by
  apply PredicateInterpretation.jointly_faithful T
  intro M _ _
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  apply ConcreteCategory.hom_ext
  intro q
  let p := (F T M).map ((lists T V).parameterNil V) q
  have hn : ((F T M).map (lists T V).algebra.nil ((F T M).map (terminal.from V) q)).val = 0 :=
    nil_value T M _ V _
  have hp : ((F T M).map (prod.snd : V ⨯ listObject T V ⟶ listObject T V) p).val = 0 := by
    change ((F T M).map (prod.snd : V ⨯ listObject T V ⟶ _)
      ((F T M).map (prod.lift (𝟙 V) (terminal.from V ≫ (lists T V).algebra.nil)) q)).val = 0
    erw [model_lift_snd T M]
    rw [Functor.map_comp_apply]
    exact hn
  have hb : ConcreteNamedSubstitution.member
      ((F T M).map (prod.fst : V ⨯ listObject T V ⟶ V) p).val
      ((F T M).map (prod.snd : V ⨯ listObject T V ⟶ listObject T V) p).val =
        (if false then (1 : M) else 0) := by simp [hp]
  rw [Functor.map_comp_apply]
  exact (membershipArrow_point T M V p false hb).trans
    (model_constant_comp T M ((lists T V).parameterNil V) q false)

theorem membershipArrow_cons :
    (lists T V).parameterCons V ≫ membershipArrow T V =
      (lists T V).parameterRec (membershipArrow T V) ≫
        StableListAlgebra.membershipStep (SyntacticDecidableVariables.decidableVariables T V) := by
  classical
  apply PredicateInterpretation.jointly_faithful T
  intro M _ _
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  apply ConcreteCategory.hom_ext
  intro q
  let x := ((F T M).map (prod.fst : V ⨯ (V ⨯ listObject T V) ⟶ V) q).val
  let y := ((F T M).map (prod.fst : V ⨯ listObject T V ⟶ V)
    ((F T M).map (prod.snd : V ⨯ (V ⨯ listObject T V) ⟶ V ⨯ listObject T V) q)).val
  let a := ((F T M).map (prod.snd : V ⨯ listObject T V ⟶ listObject T V)
    ((F T M).map (prod.snd : V ⨯ (V ⨯ listObject T V) ⟶ V ⨯ listObject T V) q)).val
  obtain ⟨b,hb⟩ : ∃ b : Bool, ConcreteNamedSubstitution.member x a = if b then 1 else 0 := by
    rcases ConcreteNamedSubstitution.member_boolean x a with h | h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  obtain ⟨e,he⟩ : ∃ e : Bool, (x = y ↔ e = true) := by
    by_cases h : x = y
    · exact ⟨true,by simp [h]⟩
    · exact ⟨false,by simp [h]⟩
  have hnew : ConcreteNamedSubstitution.member x (adjoin y a) =
      if Bool.or e b then 1 else 0 := by
    rw [ConcreteNamedSubstitution.member_adjoin]
    cases e <;> cases b <;> simp_all [eq_comm]
  let tail : V ⨯ (V ⨯ listObject T V) ⟶ V ⨯ listObject T V :=
    prod.lift prod.fst (prod.snd ≫ prod.snd)
  let names : V ⨯ (V ⨯ listObject T V) ⟶ V ⨯ V :=
    prod.lift prod.fst (prod.snd ≫ prod.fst)
  let p := (F T M).map ((lists T V).parameterCons V) q
  have hp₁ : ((F T M).map (prod.fst : V ⨯ listObject T V ⟶ V) p).val = x := by
    change ((F T M).map (prod.fst : V ⨯ listObject T V ⟶ _)
      ((F T M).map (prod.map (𝟙 V) (lists T V).algebra.cons) q)).val = x
    erw [model_map_fst T M]
    rw [Functor.map_id_apply]
    rfl
  have hp₂ : ((F T M).map (prod.snd : V ⨯ listObject T V ⟶ listObject T V) p).val =
      adjoin y a := by
    change ((F T M).map (prod.snd : V ⨯ listObject T V ⟶ _)
      ((F T M).map (prod.map (𝟙 V) (lists T V).algebra.cons) q)).val = adjoin y a
    erw [model_map_snd T M,cons_value T M V]
    rfl
  have hleft : (F T M).map ((lists T V).parameterCons V ≫ membershipArrow T V) q =
      (F T M).map (Two.constant (V ⨯ (V ⨯ listObject T V)) (Bool.or e b)) q := by
    rw [Functor.map_comp_apply]
    apply (membershipArrow_point T M V p (Bool.or e b) ?_).trans
      (model_constant_comp T M ((lists T V).parameterCons V) q (Bool.or e b))
    erw [hp₁,hp₂]
    exact hnew
  have heq : (F T M).map (names ≫ SyntacticDecidableVariables.test T V) q =
      (F T M).map (Two.constant (V ⨯ (V ⨯ listObject T V)) e) q := by
    apply equalityTest_comp_point T M V names q e
    erw [model_lift_fst T M,model_lift_snd T M]
    simpa only [Functor.map_comp_apply] using he
  have htail : (F T M).map (tail ≫ membershipArrow T V) q =
      (F T M).map (Two.constant (V ⨯ (V ⨯ listObject T V)) b) q := by
    rw [Functor.map_comp_apply]
    apply (membershipArrow_point T M V ((F T M).map tail q) b ?_).trans
      (model_constant_comp T M tail q b)
    erw [model_lift_fst T M,model_lift_snd T M]
    simpa only [Functor.map_comp_apply] using hb
  have hright : (F T M).map ((lists T V).parameterRec (membershipArrow T V) ≫
      StableListAlgebra.membershipStep (SyntacticDecidableVariables.decidableVariables T V)) q =
      (F T M).map (Two.constant (V ⨯ (V ⨯ listObject T V)) (Bool.or e b)) q := by
    rw [membership_step_reassociate]
    exact model_binary T M Bool.or (names ≫ SyntacticDecidableVariables.test T V)
      (tail ≫ membershipArrow T V) q e b heq htail
  exact hleft.trans hright.symm

/-- The numerical occurrence test is the actual categorical membership
fold, proved for every T-model by stable initiality. -/
theorem membershipArrow_eq : membershipArrow T V =
    (lists T V).membership (SyntacticDecidableVariables.decidableVariables T V) := by
  rw [(lists T V).membership_eq_parameterFold]
  exact (lists T V).parameterFold_unique (Two.constant V false)
    (StableListAlgebra.membershipStep (SyntacticDecidableVariables.decidableVariables T V))
    (membershipArrow T V) (membershipArrow_nil T V) (membershipArrow_cons T V)

end CategoricalEssentialIncompleteness.V46.ConcreteNamedComparison
