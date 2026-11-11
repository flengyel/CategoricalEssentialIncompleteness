/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.SyntacticFamily
public import CategoricalEssentialIncompleteness.ArithmeticDomainApplication
public import FailureOfComposition.UniformRange

/-! # Standard numeral observations in the uniformly provable category -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.RestrictionCategory
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition FailureOfComposition.TypedProgramCategory
open FailureOfComposition.CodedObjectMembership FailureOfComposition.ConcreteEvaluator

namespace CategoricalEssentialIncompleteness.LocalConnectedness.SyntacticModel

variable (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]

def kappa (n : ℕ) : omegaObject T ⟶ omegaObject T :=
  arrowOfIndex T .omega .omega (UniformRange.rangeConstantIndex n)

theorem kappa_model (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (n : ℕ) :
    (functor T M).map (kappa T n)=fun _ =>
      Part.some (⟨(ORingStructure.numeral n : M),memberFormula_omega_eval _⟩ : carrier M .omega) := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  apply PFun.ext
  intro x y
  rw [kappa,mem_map_index,UniformRange.eventualGraph_rangeConstantIndex_eval]
  rw [Part.mem_some_iff,Subtype.ext_iff]
  rw [numeral_eq_natCast]

def observation (c : Idem (omegaObject T)) : Set ℕ :=
  {n | kappa T n ≫ c.hom=kappa T n}

def domainFormula (q : ℕ) : 𝚺₁.Semisentence 1 :=
  .mkSigma “x. ∃ y, !(eventualGraph q).val x y”

theorem domainFormula_eval {M : Type} [ORingStructure M] (q : ℕ) (x : M) :
    (domainFormula q).val.Evalb ![x] ↔ ∃ y : M,(eventualGraph q).val.Evalb ![x,y] := by
  simp [domainFormula]

attribute [local irreducible] domainFormula normalizeIndex UniformRange.rangeConstantIndex

theorem constant_idem_eq_iff {X Y : PartialFunctions.Pfn} (x : Y) (a : Idem Y) [Nonempty X] :
    (fun _ : X => Part.some x) ≫ a.hom=(fun _ : X => Part.some x) ↔
      x ∈ PartialFunctions.support a := by
  constructor
  · intro h
    obtain ⟨z⟩ := ‹Nonempty X›
    have he := congrFun h z
    change (Part.some x).bind a.hom=Part.some x at he
    rw [Part.bind_some] at he
    exact ((PartialFunctions.mem_idem a x x).mp (Part.eq_some_iff.mp he)).1
  · intro h
    funext z
    change (Part.some x).bind a.hom=Part.some x
    rw [Part.bind_some]
    exact Part.eq_some_iff.mpr ((PartialFunctions.mem_idem a x x).mpr ⟨h,rfl⟩)

theorem numeral_domain_support (c : Idem (omegaObject T)) (q : ℕ)
    (hq : c.hom=arrowOfIndex T .omega .omega q)
    (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (n : ℕ) :
    M↓[ℒₒᵣ] ⊧ ((domainFormula (normalizeIndex .omega .omega q)).val/[
      (↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence) ↔
      (⟨(ORingStructure.numeral n : M),memberFormula_omega_eval _⟩ : carrier M .omega) ∈
        PartialFunctions.support ((rangeFunctor T M).mapIdem c) := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  rw [ClassicalPrograms.numeralInstance_eval,domainFormula_eval]
  exact (zeroDomainProgram_spec _ _).symm.trans
    (domainProgram_support T c q hq M ⟨(ORingStructure.numeral n : M),memberFormula_omega_eval _⟩)

/-- The paper's definition by provability of a numeral instance agrees with
its displayed categorical fixed-point equation, for every representative. -/
theorem observation_iff_provable (c : Idem (omegaObject T)) (q : ℕ)
    (hq : c.hom=arrowOfIndex T .omega .omega q) (n : ℕ) :
    n ∈ observation T c ↔ T ⊢ ((domainFormula (normalizeIndex .omega .omega q)).val/[
      (↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence) := by
  constructor
  · intro h
    apply Arithmetic.complete.{0} T
    intro M _ _
    apply (numeral_domain_support T c q hq M n).mpr
    have he := congrArg (fun f => (functor T M).map f) h
    simp only [CategoryTheory.Functor.map_comp,kappa_model] at he
    letI : Nonempty ((functor T M).obj (omegaObject T)) :=
      ⟨(⟨0,memberFormula_omega_eval 0⟩ : carrier M .omega)⟩
    exact (constant_idem_eq_iff _ ((rangeFunctor T M).mapIdem c)).mp he
  · intro h
    apply joint_faithful T
    intro M _ _
    simp only [CategoryTheory.Functor.map_comp,kappa_model]
    letI : Nonempty ((functor T M).obj (omegaObject T)) :=
      ⟨(⟨0,memberFormula_omega_eval 0⟩ : carrier M .omega)⟩
    apply (constant_idem_eq_iff _ ((rangeFunctor T M).mapIdem c)).mpr
    apply (numeral_domain_support T c q hq M n).mp
    exact consequence_iff.mp (Theory.Proof.sound h) M inferInstance

theorem observation_faithful_representation (c : Idem (omegaObject T)) (n : ℕ) :
    n ∈ observation T c ↔
      (familyFunctor T).map (kappa T n) ≫ (familyFunctor T).map c.hom=
        (familyFunctor T).map (kappa T n) := by
  change kappa T n ≫ c.hom=kappa T n ↔ _
  rw [← CategoryTheory.Functor.map_comp]
  exact ⟨congrArg (familyFunctor T).map,fun h => (familyFunctor T).map_injective h⟩

theorem numeral_provability_enumerable [T.RE] (C : ArithmeticSemisentence 1) :
    REPred (fun (n : ℕ) => T ⊢ (C/[(↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence)) := by
  have hc : Computable (fun (n : ℕ) => Encodable.encode (C/[(↑n : ArithmeticSemiterm Empty 0)] : ArithmeticSentence)) :=
    Computable.encode.comp (computable_numeralSubstitution.comp (Computable.const C) Computable.id)
  exact ((ArithmeticApplication.theoremCodes_re T).comp hc).of_eq
    (fun n => ArithmeticApplication.mem_theoremCodes_encode T _)

theorem observation_enumerable [T.RE] (c : Idem (omegaObject T)) :
    REPred (· ∈ observation T c) := by
  obtain ⟨q,hq⟩ := exists_arrowOfIndex T .omega .omega c.hom
  exact (numeral_provability_enumerable T
    (domainFormula (normalizeIndex .omega .omega q)).val).of_eq
      (fun n => (observation_iff_provable T c q hq.symm n).symm)

end CategoricalEssentialIncompleteness.LocalConnectedness.SyntacticModel
