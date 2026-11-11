/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.NumericalExtensionTheta.Categorical
public import FailureOfComposition.NumericalExtensionComposition.Application

/-!
# Constant-zero application of the B1(8) theta computation

The component arrow is the total constant-zero program from the B1(7)
application, not the nowhere-defined categorical zero.  Internal vacuity of
`Ext(0,i)` shows first, for arbitrary elements of every PA model, that the raw
theta graph is the second-projection graph.  The quotient equality and the
uniform supplied-proof examples follow from that statement.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.Entailment Metamath.Feferman CategoryTheory
open scoped FFL.FirstOrder.Arithmetic
open Arith.Feferman.Specialization
open CategoricalRiceShapiro.Evaluator

namespace FailureOfComposition.NumericalExtensionTheta

open CodedObjectMembership ConcreteEvaluator FiniteExtensionChecker
open NumericalExtensionComposition NumericalExtensionProofs ProofSearch
open TypedNearProduct TypedProgramCategory UniformIndexQuotient
open PCategoryStruct TypedChoice

noncomputable section

/-! ## Internal graph equality and quotient equality -/

/-- The application theta program is the second projection on every
internally coded input pair.  Both coordinates and the output are arbitrary
elements of the PA model. -/
@[simp] theorem applicationTheta_pair_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (t i y : M) :
    (eventualGraph (thetaIndex applicationZeroRepresentative)).val.Evalb
        ![pair t i, y] ↔ y = i := by
  rw [eventualGraph_thetaIndex_pair_eval]
  constructor
  · exact fun h => h.1
  · intro hy
    refine ⟨hy, 0, ?_, ?_⟩
    · rw [applicationZeroRepresentative,
        eventualGraph_normalizeIndex_eval]
      simp only [memberFormula_omega_eval, true_and, and_true]
      exact (ProgramGraph.computes_zero t 0).mpr rfl
    · rw [extensionFormula_eval_bounded]
      simp

/-- PA-uniform equality of the raw application theta program and the raw
second projection. -/
theorem pa_applicationTheta_eq_secondProjection :
    EqIndex 𝗣𝗔 (thetaIndex applicationZeroRepresentative)
      secondProjectionIndex := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, uniformSentence_eval]
  intro x y
  conv_lhs => rw [← pair_unpair x]
  rw [applicationTheta_pair_eval,
    eventualGraph_secondProjectionIndex_eval]

/-- The typed application theta arrow is the actual second projection. -/
theorem applicationTheta_eq_p1
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    thetaArrow T .omega (applicationZeroArrow T) =
      p1 (omegaObject T) (omegaObject T) := by
  apply CodedHom.ext
  let q := chosenOmegaRepresentative T .omega (applicationZeroArrow T)
  have hzero : classOf T applicationZeroRepresentative =
      (applicationZeroArrow T).val := by
    rw [applicationZeroRepresentative, applicationZeroArrow,
      TypedChoice.omegaConstantZeroArrow, arrowOfIndex_val]
  have hq : classOf T q = classOf T applicationZeroRepresentative :=
    (classOf_chosenOmegaRepresentative T .omega
      (applicationZeroArrow T)).trans hzero.symm
  have htheta : classOf T (thetaIndex q) =
      classOf T (thetaIndex applicationZeroRepresentative) := by
    simp only [thetaIndex, ← mul_classOf, ← tensorClass_classOf]
    rw [hq]
  have happ : classOf T (thetaIndex applicationZeroRepresentative) =
      classOf T secondProjectionIndex :=
    (classOf_eq_classOf_iff T _ _).mpr
      (WeakerThan.pbl pa_applicationTheta_eq_secondProjection)
  have hp1 : classOf T secondProjectionIndex =
      (p1 (omegaObject T) (omegaObject T)).val := by
    calc
      classOf T secondProjectionIndex =
          secondProjectionClass T * objectIdempotent T PairOmega := by
        rw [objectIdempotent_pairOmega, mul_one]
        rfl
      _ = (p1 (omegaObject T) (omegaObject T)).val := by
        simpa only [omegaObject, objectCode_object] using
          (p1_val T (omegaObject T) (omegaObject T)).symm
  exact (classOf_thetaRepresentative T .omega
      (applicationZeroArrow T)).symm.trans
    (htheta.trans (happ.trans hp1))

/-! ## Uniform standard proof evidence -/

theorem applicationZeroRepresentative_provable
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (t : ℕ) :
    T ⊢ (eventualGraph applicationZeroRepresentative).val/[t, (0 : ℕ)] := by
  apply WeakerThan.pbl (𝓢 := 𝗣𝗔)
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, graph_instance_eval, applicationZeroRepresentative,
    eventualGraph_normalize_constantZero_eval]
  simp only [ORingStructure.zero_eq_zero]

/-- For arbitrary external `t` and `i`, the accepted common checker contains
component, checker, and zero-test evidence, and both supplied-code maps
produce the same theta endpoint. -/
theorem reTheory_applicationThetaEvidence
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (hRE : REPred (FailureOfComposition.AxiomCodes T))
    (t i : ℕ) :
    ∃ p s x : ℕ,
      Proof_T (reTheoryExtensionThetaTheoryPresentation T hRE) p
        (rightInstanceCode applicationZeroRepresentative t 0) ∧
      Proof_T (reTheoryExtensionThetaTheoryPresentation T hRE) s
        (checkerInstanceCode 0 i) ∧
      Proof_T (reTheoryExtensionThetaTheoryPresentation T hRE) x
        (extensionInstanceCode 0 i) ∧
      Proof_T (reTheoryExtensionThetaTheoryPresentation T hRE)
        (componentAndCheckerToTheta p s
          applicationZeroRepresentative t 0 i)
        (thetaInstanceCode applicationZeroRepresentative t i) ∧
      Proof_T (reTheoryExtensionThetaTheoryPresentation T hRE)
        (componentAndExtToTheta p x
          applicationZeroRepresentative t 0 i)
        (thetaInstanceCode applicationZeroRepresentative t i) := by
  have hzero := applicationZeroRepresentative_provable T t
  have hchecker : T ⊢ (eventualGraph extensionCheckerIndex).val/[
      Nat.pair 0 i, Nat.pair 0 i] := by
    have h := extensionDomain_fixes_empty T i
    rw [extensionDomain_hom, extensionCheckerArrow_val,
      provableAt_classOf] at h
    exact h
  have hext : T ⊢ extensionFormula.val/[(0 : ℕ), i] :=
    proves_extensionFormula_zero T i
  obtain ⟨p, hp⟩ :=
    (reTheory_provable_right_iff_exists_extensionThetaProof_T
      T hRE applicationZeroRepresentative t 0).mp hzero
  obtain ⟨s, hs⟩ :=
    (reTheory_provable_checker_iff_exists_extensionThetaProof_T
      T hRE 0 i).mp hchecker
  obtain ⟨x, hx⟩ :=
    (reTheory_provable_extension_iff_exists_thetaExtensionProof_T
      T hRE 0 i).mp hext
  exact ⟨p, s, x, hp, hs, hx,
    reTheoryProof_T_componentAndCheckerToTheta T hRE hp hs,
    reTheoryProof_T_componentAndExtToTheta T hRE hp hx⟩

end

end FailureOfComposition.NumericalExtensionTheta
