/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import FailureOfComposition.TypedRanges

/-!
# Uniform numerical representatives for categorical ranges

The selected `rangeIndex q` realizes the required range graph, but its
definition makes a separate classical choice for each source index.  This file
uses the realization theorem only once.  A fixed program `uRange` receives an
encoded pair `pair q y`; it returns `y` precisely when the evaluator has a
successful computation of `q` with output `y`.  The numerical constructor
`uniformRangeIndex` first pairs its input with the external source index and
then applies this fixed program.

The fixed seed `uRange` is selected noncomputably.  No executable numeral for
it is extracted.  Nevertheless, dependence of `uniformRangeIndex q` on the
varying index `q` is primitive recursive.  Its graph equation holds for all
internal inputs and outputs in every model of PA, and its PA-uniform class is
the class of the existing selected range representative.
-/

@[expose] public section

set_option autoImplicit false

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory CategoricalRiceShapiro.Evaluator
open CategoricalRiceShapiro.PartialRecursive

namespace FailureOfComposition.UniformRange

open CodedObjectMembership ConcreteEvaluator ConcreteIndices ProgramGraph
open ProofSearch SigmaOneRealization TypedNearProduct TypedProgramCategory
open TypedRanges UniformIndexQuotient

noncomputable section

/-! ## Effective parameter programs -/

/-- The production index of the total constant program with value `q`. -/
def rangeConstantIndex (q : ℕ) : ℕ :=
  encode (Nat.Partrec.Code.const q)

/-- The program that sends `y` to `pair q y`. -/
def rangeParameterIndex (q : ℕ) : ℕ :=
  pairIndex (rangeConstantIndex q) Kleene.identityIndex

theorem primrec_rangeConstantIndex : Primrec rangeConstantIndex :=
  Primrec.encode.comp Nat.Partrec.Code.primrec_const

theorem primrec_rangeParameterIndex : Primrec rangeParameterIndex :=
  primrec₂_pairIndex.comp primrec_rangeConstantIndex
    (Primrec.const Kleene.identityIndex)

@[simp] theorem eventualGraph_rangeConstantIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q : ℕ) (x y : M) :
    (eventualGraph (rangeConstantIndex q)).val.Evalb ![x, y] ↔
      y = (q : M) := by
  change Computes (Nat.Partrec.Code.const q) x y ↔ _
  exact computes_const q x y

@[simp] theorem eventualGraph_rangeParameterIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q : ℕ) (y a : M) :
    (eventualGraph (rangeParameterIndex q)).val.Evalb ![y, a] ↔
      a = pair (q : M) y := by
  rw [rangeParameterIndex, eventualGraph_pairIndex_eval]
  constructor
  · rintro ⟨u, v, hu, hv, rfl⟩
    have hu' := (eventualGraph_rangeConstantIndex_eval q y u).mp hu
    have hv' := (eventualGraph_identityIndex_eval y v).mp hv
    subst u
    subst v
    rfl
  · rintro rfl
    exact ⟨(q : M), y,
      (eventualGraph_rangeConstantIndex_eval q y _).mpr rfl,
      (eventualGraph_identityIndex_eval y _).mpr rfl, rfl⟩

/-! ## One fixed universal range-search graph -/

/-- The fixed graph receives `a = pair e y` and returns `y` when the production
evaluator has a computation of the internally supplied code `e` with output
`y`.  The certificate arguments have order `(s,e,x,y)`. -/
def universalRangeGraph : Graph := .mkSigma
  “a z. ∃ e y, !natPairFormula.val a e y ∧ z = y ∧
    ∃ x s, !evalnCertificateFormula.val s e x y”

private theorem universalRangeGraph_raw_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (a z : M) :
    universalRangeGraph.val.Evalb ![a, z] ↔
      ∃ e y : M, a = pair e y ∧ z = y ∧
        ∃ x s : M, Semiformula.Evalb ![s, e, x, y]
          (evalnCertificateFormula : ArithmeticSemisentence 4) := by
  simp [universalRangeGraph]

/-- Projection form of the universal graph.  Its output is forced by the
second projection, without using functionality of an internally supplied
program code. -/
@[simp] theorem universalRangeGraph_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (a z : M) :
    universalRangeGraph.val.Evalb ![a, z] ↔
      z = pi₂ a ∧ ∃ x s : M,
        Semiformula.Evalb ![s, pi₁ a, x, pi₂ a]
          (evalnCertificateFormula : ArithmeticSemisentence 4) := by
  rw [universalRangeGraph_raw_eval]
  constructor
  · rintro ⟨e, y, ha, hz, x, s, hs⟩
    have he : pi₁ a = e := by simpa only [pi₁_pair] using congrArg pi₁ ha
    have hy : pi₂ a = y := by simpa only [pi₂_pair] using congrArg pi₂ ha
    exact ⟨hz.trans hy.symm, x, s, by simpa only [he, hy] using hs⟩
  · rintro ⟨hz, x, s, hs⟩
    exact ⟨pi₁ a, pi₂ a, (pair_unpair a).symm, hz, x, s, hs⟩

/-- PA proves that the fixed universal graph is functional because its output
is the second projection of its input. -/
theorem universalRangeGraph_functional : Functional universalRangeGraph := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, functionalSentence_eval]
  intro a y z hy hz
  exact (universalRangeGraph_eval a y).mp hy |>.1 |>.trans
    ((universalRangeGraph_eval a z).mp hz |>.1).symm

/-- A single fixed realizer of `universalRangeGraph`.  This is the only
classical program-index choice in the uniform construction. -/
def uRange : ℕ :=
  Classical.choose (realize_graph universalRangeGraph
    universalRangeGraph_functional)

theorem uRange_realizes :
    Uniform 𝗣𝗔 (eventualGraph uRange) universalRangeGraph :=
  Classical.choose_spec (realize_graph universalRangeGraph
    universalRangeGraph_functional)

@[simp] theorem eventualGraph_uRange_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (a z : M) :
    (eventualGraph uRange).val.Evalb ![a, z] ↔
      z = pi₂ a ∧ ∃ x s : M,
        Semiformula.Evalb ![s, pi₁ a, x, pi₂ a]
          (evalnCertificateFormula : ArithmeticSemisentence 4) := by
  have h := consequence_iff.mp (Theory.Proof.sound uRange_realizes) M inferInstance
  rw [models_iff, uniformSentence_eval] at h
  exact (h a z).trans (universalRangeGraph_eval a z)

/-! ## The primitive-recursive uniform range representative -/

/-- The uniform range representative.  Its first stage maps `y` to
`pair q y`; the fixed outer program `uRange` then searches for a computation
of `q` with output `y`. -/
def uniformRangeIndex (q : ℕ) : ℕ :=
  compIndex uRange (rangeParameterIndex q)

/-- The range representative depends primitive recursively on every varying
source program index.  The noncomputably selected `uRange` is one fixed
external constant. -/
theorem primrec_uniformRangeIndex : Primrec uniformRangeIndex :=
  primrec₂_compIndex.comp (Primrec.const uRange)
    primrec_rangeParameterIndex

/-- Exact graph law for each external source index in every model of PA.  The
preimage, input, and output are internal model elements. -/
@[simp] theorem eventualGraph_uniformRangeIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (q : ℕ) (y z : M) :
    (eventualGraph (uniformRangeIndex q)).val.Evalb ![y, z] ↔
      y = z ∧ ∃ x : M, (eventualGraph q).val.Evalb ![x, y] := by
  rw [uniformRangeIndex, eventualGraph_comp_eval]
  constructor
  · rintro ⟨a, ha, hz⟩
    have ha' := (eventualGraph_rangeParameterIndex_eval q y a).mp ha
    subst a
    obtain ⟨hzy, x, s, hs⟩ :=
      (eventualGraph_uRange_eval (pair (q : M) y) z).mp hz
    simp only [pi₁_pair, pi₂_pair] at hzy hs
    refine ⟨hzy.symm, x, (eventualGraph_eval q _).mpr ⟨s, ?_⟩⟩
    simpa only [numeral_eq_natCast_app, Matrix.cons_val_zero,
      Matrix.cons_val_one] using hs
  · rintro ⟨hyz, x, hx⟩
    obtain ⟨s, hs⟩ := (eventualGraph_eval q _).mp hx
    refine ⟨pair (q : M) y,
      (eventualGraph_rangeParameterIndex_eval q y _).mpr rfl, ?_⟩
    apply (eventualGraph_uRange_eval (pair (q : M) y) z).mpr
    refine ⟨by simpa only [pi₂_pair] using hyz.symm, x, s, ?_⟩
    simpa only [pi₁_pair, pi₂_pair, numeral_eq_natCast_app,
      Matrix.cons_val_zero, Matrix.cons_val_one] using hs

/-- PA proves the uniform graph equation with the existing range graph. -/
theorem uniformRangeIndex_realizes (q : ℕ) :
    Uniform 𝗣𝗔 (eventualGraph (uniformRangeIndex q)) (rangeGraph q) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, uniformSentence_eval]
  intro y z
  have hr := rangeGraph_eval (M := M) q ![y, z]
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one] using
    (eventualGraph_uniformRangeIndex_eval q y z).trans hr.symm

/-- In the standard model, `uniformRangeIndex q` is the partial identity on
the actual range of the partial function with index `q`. -/
theorem uniformRangeIndex_eval (q y z : ℕ) :
    z ∈ Kleene.eval (uniformRangeIndex q) y ↔
      y = z ∧ ∃ x : ℕ, y ∈ Kleene.eval q x := by
  rw [← eventualGraph_adequate]
  simpa only [eventualGraph_adequate] using
    eventualGraph_uniformRangeIndex_eval q y z

/-- The uniform representative and the existing selected representative have
the same graph uniformly in PA.  This is equality in the maintained uniform
index relation, not literal equality of natural-number codes. -/
theorem eqIndex_uniformRangeIndex_rangeIndex (q : ℕ) :
    EqIndex 𝗣𝗔 (uniformRangeIndex q) (rangeIndex q) :=
  rangeIndex_realization_unique (uniformRangeIndex_realizes q)
    (rangeIndex_realizes q)

theorem eqIndex_uniformRangeIndex_rangeIndex_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] (q : ℕ) :
    EqIndex T (uniformRangeIndex q) (rangeIndex q) :=
  WeakerThan.pbl (eqIndex_uniformRangeIndex_rangeIndex q)

/-- Uniformly provably equal source representatives have uniformly provably
equal range representatives. -/
theorem eqIndex_uniformRangeIndex_congr
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] {q r : ℕ}
    (h : EqIndex T q r) :
    EqIndex T (uniformRangeIndex q) (uniformRangeIndex r) :=
  uniform_trans (WeakerThan.pbl (uniformRangeIndex_realizes q))
    (uniform_trans (uniform_rangeOfGraph_in T h)
      (uniform_symm (WeakerThan.pbl (uniformRangeIndex_realizes r))))

/-! ## Typed uniform range representatives -/

/-- The uniform range representative of the normalized typed program. -/
def typedUniformRangeIndex
    (Q R : STObjectCode) (q : ℕ) : ℕ :=
  uniformRangeIndex (normalizeIndex Q R q)

/-- For fixed external object codes, the typed representative is primitive
recursive in the varying raw source index. -/
theorem primrec_typedUniformRangeIndex (Q R : STObjectCode) :
    Primrec (typedUniformRangeIndex Q R) :=
  primrec_uniformRangeIndex.comp (primrec_normalizeIndex Q R)

@[simp] theorem eventualGraph_typedUniformRangeIndex_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (Q R : STObjectCode) (q : ℕ) (y z : M) :
    (eventualGraph (typedUniformRangeIndex Q R q)).val.Evalb ![y, z] ↔
      y = z ∧ ∃ x : M,
        (eventualGraph (normalizeIndex Q R q)).val.Evalb ![x, y] :=
  eventualGraph_uniformRangeIndex_eval (normalizeIndex Q R q) y z

/-- The typed graph equation with normalization expanded. -/
@[simp] theorem eventualGraph_typedUniformRangeIndex_normalized_eval
    {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
    (Q R : STObjectCode) (q : ℕ) (y z : M) :
    (eventualGraph (typedUniformRangeIndex Q R q)).val.Evalb ![y, z] ↔
      y = z ∧ (memberFormula R).val.Evalb ![y] ∧
        ∃ x : M, (memberFormula Q).val.Evalb ![x] ∧
          (eventualGraph q).val.Evalb ![x, y] := by
  rw [eventualGraph_typedUniformRangeIndex_eval]
  constructor
  · rintro ⟨hyz, x, hnorm⟩
    obtain ⟨hQ, hq, hR⟩ :=
      (eventualGraph_normalizeIndex_eval Q R q x y).mp hnorm
    exact ⟨hyz, hR, x, hQ, hq⟩
  · rintro ⟨hyz, hR, x, hQ, hq⟩
    exact ⟨hyz, x,
      (eventualGraph_normalizeIndex_eval Q R q x y).mpr ⟨hQ, hq, hR⟩⟩

theorem typedUniformRangeIndex_uniform
    (Q R : STObjectCode) (q : ℕ) :
    Uniform 𝗣𝗔 (eventualGraph (typedUniformRangeIndex Q R q))
      (rangeGraph (normalizeIndex Q R q)) :=
  uniformRangeIndex_realizes (normalizeIndex Q R q)

theorem typedUniformRangeIndex_normalized_uniform
    (Q R : STObjectCode) (q : ℕ) :
    Uniform 𝗣𝗔 (eventualGraph (typedUniformRangeIndex Q R q))
      (typedRangeGraph Q R q) :=
  uniform_trans (typedUniformRangeIndex_uniform Q R q)
    (uniform_rangeOfGraph (normalizeIndex_uniform Q R q))

/-- The raw uniform range program is supported as an endomorphism of the
declared target object. -/
theorem pa_proves_typedUniformRangeIndex_support
    (Q R : STObjectCode) (q : ℕ) :
    𝗣𝗔 ⊢ supportSentence R R (typedUniformRangeIndex Q R q) := by
  apply complete.{0} 𝗣𝗔
  intro M _ _
  rw [models_iff, supportSentence_eval]
  intro y z h
  obtain ⟨hyz, hR, _⟩ :=
    (eventualGraph_typedUniformRangeIndex_normalized_eval Q R q y z).mp h
  exact ⟨hR, by simpa only [hyz] using hR⟩

/-- Target normalization does not change the uniform range representative's
class in any extension of PA. -/
theorem typedUniformRangeIndex_normalize_eq
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) (q : ℕ) :
    EqIndex T
      (normalizeIndex R R (typedUniformRangeIndex Q R q))
      (typedUniformRangeIndex Q R q) :=
  (proves_support_iff_eqIndex_normalize T R R
    (typedUniformRangeIndex Q R q)).mp
      (WeakerThan.pbl (pa_proves_typedUniformRangeIndex_support Q R q))

/-- PA-uniform equality with the previously selected typed range
representative. -/
theorem eqIndex_typedUniformRangeIndex_typedRangeIndex
    (Q R : STObjectCode) (q : ℕ) :
    EqIndex 𝗣𝗔 (typedUniformRangeIndex Q R q)
      (typedRangeIndex Q R q) :=
  rangeIndex_realization_unique
    (typedUniformRangeIndex_uniform Q R q)
    (typedRangeIndex_uniform Q R q)

theorem eqIndex_typedUniformRangeIndex_typedRangeIndex_in
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) (q : ℕ) :
    EqIndex T (typedUniformRangeIndex Q R q)
      (typedRangeIndex Q R q) :=
  WeakerThan.pbl
    (eqIndex_typedUniformRangeIndex_typedRangeIndex Q R q)

/-- The actual categorical range is represented by the uniform numerical
constructor. -/
theorem rangeArrow_arrowOfIndex_eq_uniformRange
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) (q : ℕ) :
    rangeArrow T (arrowOfIndex T Q R q) =
      arrowOfIndex T R R (typedUniformRangeIndex Q R q) :=
  rangeArrow_eq_arrowOfIndex_of_realizes T Q R q
    (typedUniformRangeIndex Q R q)
    (typedUniformRangeIndex_uniform Q R q)

theorem ran_arrowOfIndex_eq_uniformRange
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) (q : ℕ) :
    HasRanges.ran (arrowOfIndex T Q R q) =
      arrowOfIndex T R R (typedUniformRangeIndex Q R q) :=
  rangeArrow_arrowOfIndex_eq_uniformRange T Q R q

/-- Typed normalized representatives that are uniformly equal have uniformly
equal typed range representatives. -/
theorem eqIndex_typedUniformRangeIndex_congr
    (T : ArithmeticTheory) [𝗣𝗔 ⪯ T]
    (Q R : STObjectCode) {q r : ℕ}
    (h : EqIndex T (normalizeIndex Q R q) (normalizeIndex Q R r)) :
    EqIndex T (typedUniformRangeIndex Q R q)
      (typedUniformRangeIndex Q R r) :=
  eqIndex_uniformRangeIndex_congr T h

end

end FailureOfComposition.UniformRange
