/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.ConcreteAdequacy
public import FailureOfComposition.FiniteFunctionCoding
public import FailureOfComposition.SigmaOneRealization
public import FailureOfComposition.TypedNearProduct

/-!
# The finite-function evaluator

This module constructs the approximation morphism `alpha` for the concrete
finite-function coding.  Its source is the typed near product of two number
objects: the first input is a finite-function code and the second is the
argument of that finite function.  The output is the unique value selected by
`FiniteEntryModel`.

The graph is defined before its realizing production index.  Its principal law
quantifies the code, input, and output internally over an arbitrary model of
PA.  The selected index is external and fixed; no effective dependence on a
formula or on an opaque derivation is asserted.
-/

@[expose] public section

set_option autoImplicit false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open CategoryTheory CategoricalRiceShapiro.PartialRecursive
open PCategoryStruct

namespace FailureOfComposition.FiniteFunctionEvaluator

open CodedObjectMembership ConcreteEvaluator FiniteFunctionCoding
open ProofSearch SigmaOneRealization TypedNearProduct TypedProgramCategory
open UniformIndexQuotient

noncomputable section

/-! ## The finite-function graph and its production index -/

/-- The graph of finite-function evaluation.  On paired input `(c, x)`, its
output `v` is the value selected by the finite entry relation for code `c` at
input `x`. -/
def alphaGraph : Graph := .mkSigma
  “z v. ∃ c, ∃ x,
    !natPairFormula.val z c x ∧ !finiteEntryFormula.val c x v”

@[simp] theorem alphaGraph_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (z v : M) :
    alphaGraph.val.Evalb ![z, v] ↔
      FiniteEntryModel (pi₁ z) (pi₂ z) v := by
  rw [show alphaGraph.val.Evalb ![z, v] ↔
      ∃ c x : M, z = pair c x ∧ FiniteEntryModel c x v by
    simp [alphaGraph]]
  constructor
  · rintro ⟨c, x, rfl, hentry⟩
    simpa only [pi₁_pair, pi₂_pair] using hentry
  · intro hentry
    exact ⟨pi₁ z, pi₂ z, (pair_unpair z).symm, hentry⟩

/-- Finite-function evaluation is functional in PA because the least selected
output at a fixed code and input is unique. -/
theorem alphaGraph_functional : Functional alphaGraph := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  have : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ :=
    models_of_subtheory (U := 𝗣𝗔) inferInstance
  rw [models_iff, functionalSentence_eval]
  intro z v w hv hw
  exact finiteEntryModel_functional
    ((alphaGraph_eval z v).mp hv) ((alphaGraph_eval z w).mp hw)

/-- One fixed external production index realizing finite-function evaluation. -/
def alphaIndex : ℕ :=
  Classical.choose (realize_graph alphaGraph alphaGraph_functional)

/-- PA proves that the selected production index has exactly `alphaGraph`. -/
theorem alphaIndex_uniform :
    Uniform 𝗣𝗔 (eventualGraph alphaIndex) alphaGraph :=
  Classical.choose_spec (realize_graph alphaGraph alphaGraph_functional)

@[simp] theorem eventualGraph_alphaIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (z v : M) :
    (eventualGraph alphaIndex).val.Evalb ![z, v] ↔
      FiniteEntryModel (pi₁ z) (pi₂ z) v := by
  have h := consequence_iff.mp (Theory.Proof.sound alphaIndex_uniform)
    M inferInstance
  rw [models_iff, uniformSentence_eval] at h
  exact (h z v).trans (alphaGraph_eval z v)

/-- The graph law at an explicitly paired input.  The code, input, and output
are arbitrary elements of the ambient PA model. -/
@[simp] theorem eventualGraph_alphaIndex_pair_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (c x v : M) :
    (eventualGraph alphaIndex).val.Evalb ![pair c x, v] ↔
      FiniteEntryModel c x v := by
  simpa only [pi₁_pair, pi₂_pair] using
    eventualGraph_alphaIndex_eval (pair c x) v

/-- In the standard model, the selected production program evaluates a coded
finite function exactly at its selected finite entries. -/
theorem alphaIndex_computes_iff (c x v : ℕ) :
    v ∈ Kleene.eval alphaIndex (Nat.pair c x) ↔
      FiniteEntry c x v := by
  have hgraph :
      (eventualGraph alphaIndex).val.Evalb ![Nat.pair c x, v] ↔
        FiniteEntry c x v := by
    have hfinite :
        FiniteEntryModel c x v ↔ FiniteEntry c x v := by
      simpa only [numeral_eq_natCast, natCast_nat] using
        (finiteEntryModel_numeral_iff (M := ℕ) c x v)
    exact (by
      simpa only [nat_pair_eq] using
        (eventualGraph_alphaIndex_pair_eval (M := ℕ) c x v).trans
          hfinite)
  exact (eventualGraph_adequate alphaIndex (Nat.pair c x) v).symm.trans
    hgraph

/-! ## The typed approximation morphism -/

/-- Every element of a PA model belongs to the coded product of two number
objects. -/
@[simp] theorem memberFormula_alphaSource_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (z : M) :
    (memberFormula (.product .omega .omega)).val.Evalb ![z] := by
  apply (memberFormula_product_eval .omega .omega z).mpr
  exact ⟨pi₁ z, pi₂ z, (pair_unpair z).symm,
    memberFormula_omega_eval _, memberFormula_omega_eval _⟩

/-- The raw finite-function evaluator is supported from `Omega product Omega`
to `Omega`. -/
theorem pa_proves_alphaIndex_support :
    𝗣𝗔 ⊢ supportSentence (.product .omega .omega) .omega alphaIndex := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, supportSentence_eval]
  intro z v _
  exact ⟨memberFormula_alphaSource_eval z, memberFormula_omega_eval v⟩

/-- Source-target normalization does not change the finite-function evaluator
in any arithmetic theory whose provability includes PA. -/
theorem eqIndex_normalize_alphaIndex
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    EqIndex T (normalizeIndex (.product .omega .omega) .omega alphaIndex)
      alphaIndex :=
  (proves_support_iff_eqIndex_normalize T
    (.product .omega .omega) .omega alphaIndex).mp
      (WeakerThan.pbl pa_proves_alphaIndex_support)

/-- The normalized representative retains the same internal graph law. -/
@[simp] theorem eventualGraph_normalize_alphaIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (z v : M) :
    (eventualGraph
        (normalizeIndex (.product .omega .omega) .omega alphaIndex)).val.Evalb
        ![z, v] ↔
      FiniteEntryModel (pi₁ z) (pi₂ z) v := by
  rw [eventualGraph_normalizeIndex_eval, eventualGraph_alphaIndex_eval]
  simp only [memberFormula_alphaSource_eval, memberFormula_omega_eval,
    true_and, and_true]

/-- The concrete approximation morphism
`alpha : Omega product Omega ⟶ Omega`. -/
def alphaArrow
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    nearProd (omegaObject T) (omegaObject T) ⟶ omegaObject T :=
  arrowOfIndex T (.product .omega .omega) .omega alphaIndex

/-- The fixed external index `alphaIndex` is a representative of the typed
approximation morphism. -/
@[simp] theorem alphaArrow_val
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] :
    (alphaArrow T).1 = classOf T alphaIndex := by
  rw [alphaArrow, arrowOfIndex_val, classOf_eq_classOf_iff]
  exact eqIndex_normalize_alphaIndex T

end

end FailureOfComposition.FiniteFunctionEvaluator
