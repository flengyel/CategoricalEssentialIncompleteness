/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.SyntacticObservations

/-! # Finite meets and bounds of standard observations -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.TypedProgramCategory FailureOfComposition.CodedObjectMembership

namespace CategoricalEssentialIncompleteness.LocalConnectedness

theorem fixed_inf_iff {C : Type} [Category C] [RestrictionCategory C]
    {X Y : C} (f : X ⟶ Y) (a b : Idem Y) :
    f ≫ (a ⊓ b).hom=f ↔ f ≫ a.hom=f ∧ f ≫ b.hom=f := by
  change f ≫ (a.hom ≫ b.hom)=f ↔ _
  constructor
  · intro h
    have ha := congrArg (fun k : X ⟶ Y => k ≫ a.hom) h
    have hb := congrArg (fun k : X ⟶ Y => k ≫ b.hom) h
    have hca : a.hom ≫ b.hom ≫ a.hom=a.hom ≫ b.hom := by
      rw [b.comm a,← Category.assoc,a.idem]
    simp only [Category.assoc,hca] at ha
    simp only [Category.assoc,b.idem] at hb
    exact ⟨ha.symm.trans h,hb.symm.trans h⟩
  · rintro ⟨ha,hb⟩
    rw [← Category.assoc,ha,hb]

namespace SyntacticModel

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

theorem kappa_total (n : ℕ) : isTotal (kappa T n) := by
  change rst (kappa T n)=𝟙 (omegaObject T)
  apply joint_faithful T
  intro M _ _
  rw [map_restriction,kappa_model,(functor T M).map_id]
  apply PFun.ext
  intro x y
  rw [PartialFunctions.mem_rst]
  change ((∃ z,z ∈ Part.some
    (⟨(ORingStructure.numeral n : M),memberFormula_omega_eval _⟩ : carrier M .omega)) ∧ y=x) ↔
      y ∈ Part.some x
  simp only [Part.mem_some_iff,exists_eq,true_and]

theorem observation_mono {c d : Idem (omegaObject T)} (h : c ≤ d) :
    observation T c ⊆ observation T d := by
  intro n hn
  change kappa T n ≫ d.hom=kappa T n
  calc
    kappa T n ≫ d.hom=(kappa T n ≫ c.hom) ≫ d.hom := by rw [hn]
    _ =kappa T n ≫ c.hom := by rw [Category.assoc,Idem.le_def.mp h]
    _ =kappa T n := hn

theorem observation_inf (c d : Idem (omegaObject T)) :
    observation T (c ⊓ d)=observation T c ∩ observation T d := by
  ext n
  exact fixed_inf_iff (kappa T n) c d

theorem observation_top : observation T (⊤ : Idem (omegaObject T))=Set.univ := by
  ext n
  simp only [observation,Idem.top_hom,Category.comp_id,Set.mem_setOf_eq,Set.mem_univ,true_iff]

theorem kappa_nonzero (hT : Consistent T) (n : ℕ) : kappa T n≠0 := by
  obtain ⟨s⟩ := modelIndex_nonempty T hT
  letI := s.val
  letI := s.property
  intro h
  have he := congrArg (fun f => (functor T ℕ).map f) h
  rw [kappa_model,map_zero] at he
  have hz := congrFun he (⟨0,memberFormula_omega_eval 0⟩ : carrier ℕ .omega)
  change Part.some _=Part.none at hz
  have hm := Part.mem_some (⟨(ORingStructure.numeral n : ℕ),memberFormula_omega_eval _⟩ : carrier ℕ .omega)
  rw [hz] at hm
  exact hm.1

theorem observation_bot (hT : Consistent T) :
    observation T (⊥ : Idem (omegaObject T))=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro n hn
  change kappa T n ≫ (0 : omegaObject T ⟶ omegaObject T)=kappa T n at hn
  rw [CategoryTheory.Limits.comp_zero] at hn
  exact kappa_nonzero T hT n hn.symm

end SyntacticModel
end CategoricalEssentialIncompleteness.LocalConnectedness
