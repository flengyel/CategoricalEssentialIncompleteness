/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

public import CategoricalEssentialIncompleteness.V46FiniteSigmaOne
public import CategoricalEssentialIncompleteness.V46SyntacticPredicatesLimits
public import Mathlib.Tactic.FinCases

/-! # Finite value records for arbitrary list algebras in parameter slices -/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open CategoryTheory
open FailureOfComposition FailureOfComposition.ProofSearch FailureOfComposition.ConcreteEvaluator
open FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.LocalConnectedness
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticListEvaluation

/-- The cons graph reads parameter, entry, previous value and new value. -/
abbrev ConsGraph := 𝚺₁.Semisentence 4

def nilOverSentence (q n : Graph) : ArithmeticSentence :=
  “∀ p x, !n.val p x → !q.val x p”

def consSupportSentence (P V X : Carrier) (q : Graph) (c : ConsGraph) : ArithmeticSentence :=
  “∀ p v x y, !c.val p v x y →
    !P.val p ∧ !V.val v ∧ !X.val x ∧ !q.val x p ∧ !X.val y ∧ !q.val y p”

def consTotalSentence (P V X : Carrier) (q : Graph) (c : ConsGraph) : ArithmeticSentence :=
  “∀ p v x, !P.val p → !V.val v → !X.val x → !q.val x p → ∃! y, !c.val p v x y”

/-- These are exactly graph-defined algebra operations over an arbitrary
projection X→P. No evaluator or recursion principle is included as data. -/
structure SliceAlgebra (T : ArithmeticTheory) (P V X : Carrier) where
  projection : GraphMorphism T X P
  nilOp : GraphMorphism T P X
  nil_over : T ⊢ nilOverSentence projection.graph nilOp.graph
  consOp : ConsGraph
  cons_support : T ⊢ consSupportSentence P V X projection.graph consOp
  cons_total : T ⊢ consTotalSentence P V X projection.graph consOp

/-- The actual Sigma-one carrier of canonical V-lists. -/
def listCarrier (V : Carrier) : Carrier := FiniteSigmaOne.finiteMembership V

namespace SliceAlgebra

variable {T : ArithmeticTheory} {P V X : Carrier} (A : SliceAlgebra T P V X)

section Model

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

/-- A value in the fiber of the given projection over p. -/
def Fiber (p y : M) : Prop := X.val.Evalb ![y] ∧ A.projection.graph.val.Evalb ![y, p]

theorem nil_fiber (p y : M) (h : A.nilOp.graph.val.Evalb ![p, y]) : A.Fiber p y := by
  refine ⟨(A.nilOp.support_model M p y h).2, ?_⟩
  have hn := consequence_iff.mp (Theory.Proof.sound A.nil_over) M inferInstance
  have hn' : ∀ p x : M, A.nilOp.graph.val.Evalb ![p, x] →
      A.projection.graph.val.Evalb ![x, p] := by
    simpa [models_iff, nilOverSentence] using hn
  exact hn' p y h

theorem cons_support_model (p v x y : M) (h : A.consOp.val.Evalb ![p, v, x, y]) :
    P.val.Evalb ![p] ∧ V.val.Evalb ![v] ∧ A.Fiber p x ∧ A.Fiber p y := by
  have hc := consequence_iff.mp (Theory.Proof.sound A.cons_support) M inferInstance
  have hc' : ∀ p v x y : M, A.consOp.val.Evalb ![p, v, x, y] →
      P.val.Evalb ![p] ∧ V.val.Evalb ![v] ∧ X.val.Evalb ![x] ∧
        A.projection.graph.val.Evalb ![x, p] ∧ X.val.Evalb ![y] ∧
          A.projection.graph.val.Evalb ![y, p] := by
    simpa [models_iff, consSupportSentence] using hc
  obtain ⟨hp, hv, hx, hxp, hy, hyp⟩ := hc' p v x y h
  exact ⟨hp, hv, ⟨hx, hxp⟩, ⟨hy, hyp⟩⟩

theorem cons_total_model (p v x : M) (hp : P.val.Evalb ![p])
    (hv : V.val.Evalb ![v]) (hx : A.Fiber p x) :
    ∃! y : M, A.consOp.val.Evalb ![p, v, x, y] := by
  have hc := consequence_iff.mp (Theory.Proof.sound A.cons_total) M inferInstance
  have hc' : ∀ p v x : M, P.val.Evalb ![p] → V.val.Evalb ![v] →
      X.val.Evalb ![x] → A.projection.graph.val.Evalb ![x, p] →
        ∃! y : M, A.consOp.val.Evalb ![p, v, x, y] := by
    simpa [models_iff, consTotalSentence] using hc
  exact hc' p v x hp hv hx.1 hx.2

theorem cons_functional_model (p v x y z : M)
    (hy : A.consOp.val.Evalb ![p, v, x, y])
    (hz : A.consOp.val.Evalb ![p, v, x, z]) : y = z := by
  obtain ⟨hp, hv, hx, _⟩ := A.cons_support_model p v x y hy
  exact (A.cons_total_model p v x hp hv hx).unique hy hz

end Model

/-- The same Σ1 definition is used at every model, including all traces
of the graph-defined operations and reads of the numerical value vector. -/
def recordFormula : 𝚺₁.Semisentence 5 :=
  let q := A.projection.graph
  let n := A.nilOp.graph
  let c := A.consOp
  .mkSigma “p a s k b. ∃ l, !lenDef.val l b ∧ l = k + 1 ∧
    (∀ i < l, ∃ z, !nthDef.val z b i ∧ !X.val z ∧ !q.val z p) ∧
    (∃ z, !nthDef.val z b k ∧ !n.val p z) ∧
    ∀ i < k, ∃ v x y, !nthDef.val v a (s + i) ∧
      !nthDef.val x b (i + 1) ∧ !nthDef.val y b i ∧ !c.val p v x y”

section ArithmeticModel

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [M↓[ℒₒᵣ] ⊧* T]

/-- A record stores outputs in reverse evaluation order: position k
is nil, and each preceding position is the cons result using the next one. -/
def Record (p a s k b : M) : Prop :=
  len b = k + 1 ∧ (∀ i < len b, A.Fiber p (nth b i)) ∧
    A.nilOp.graph.val.Evalb ![p, nth b k] ∧
      ∀ i < k, A.consOp.val.Evalb ![p, nth a (s + i), nth b (i + 1), nth b i]

omit [M↓[ℒₒᵣ] ⊧* T] in
@[simp] theorem recordFormula_eval (p a s k b : M) :
    A.recordFormula.val.Evalb ![p, a, s, k, b] ↔ A.Record p a s k b := by
  simp [recordFormula, Record, Fiber]

omit [M↓[ℒₒᵣ] ⊧* T] in
@[simp] theorem recordFormula_eval_vec (v : Fin 5 → M) :
    A.recordFormula.val.Evalb v ↔ A.Record (v 0) (v 1) (v 2) (v 3) (v 4) := by
  have hv : ![v 0, v 1, v 2, v 3, v 4] = v := by
    funext i
    fin_cases i <;> rfl
  simpa only [hv] using A.recordFormula_eval (v 0) (v 1) (v 2) (v 3) (v 4)

instance record_definable :
    𝚺₁.Definable (fun v : Fin 5 → M => A.Record (v 0) (v 1) (v 2) (v 3) (v 4)) := by
  refine ⟨A.recordFormula.rew Rew.emb, ?_⟩
  intro v
  simp

omit [M↓[ℒₒᵣ] ⊧* T] in
theorem Record.output_fiber {p a s k b : M} (h : A.Record p a s k b) :
    A.Fiber p (nth b 0) :=
  h.2.1 0 (by rw [h.1]; simp)

theorem record_nil (p a s y : M) (hy : A.nilOp.graph.val.Evalb ![p, y]) :
    A.Record p a s 0 (adjoin y 0) := by
  refine ⟨by simp, ?_, ?_, ?_⟩
  · intro i hi
    have hi0 : i = 0 := by simpa using hi
    subst i
    simpa using A.nil_fiber p y hy
  · simpa using hy
  · intro i hi
    simp at hi

/-- Prepending one computed value extends a suffix evaluation record. -/
theorem record_prepend {p a s k b y : M} (h : A.Record p a (s + 1) k b)
    (hy : A.consOp.val.Evalb ![p, nth a s, nth b 0, y]) :
    A.Record p a s (k + 1) (adjoin y b) := by
  refine ⟨by simp [h.1], ?_, ?_, ?_⟩
  · intro i hi
    rcases zero_or_succ i with rfl | ⟨j, rfl⟩
    · simpa using (A.cons_support_model p (nth a s) (nth b 0) y hy).2.2.2
    · have hj : j < len b := by simpa using hi
      simpa using h.2.1 j hj
  · simpa using h.2.2.1
  · intro i hi
    rcases zero_or_succ i with rfl | ⟨j, rfl⟩
    · simpa using hy
    · have hj : j < k := by simpa using hi
      simp only [nth_adjoin_succ]
      simpa only [add_assoc, add_comm 1 j] using h.2.2.2 j hj

/-- Internal successor induction builds records at arbitrary model lengths.
The list membership assumption is held fixed while suffixes are evaluated. -/
theorem record_exists (p a : M) (hp : P.val.Evalb ![p])
    (ha : ∀ i < len a, V.val.Evalb ![nth a i]) :
    ∃ b : M, A.Record p a 0 (len a) b := by
  have hs : ∀ k ≤ len a, ∃ b : M, A.Record p a (len a - k) k b := by
    intro k hk
    induction k using ISigma1.sigma1_succ_induction
    · definability
    case zero =>
      obtain ⟨y, hy, _⟩ := A.nilOp.total_model M p hp
      exact ⟨adjoin y 0, A.record_nil p a (len a - 0) y hy⟩
    case succ k ih =>
      have hk' : k < len a := Arithmetic.succ_le_iff_lt.mp hk
      obtain ⟨b, hb⟩ := ih (le_trans (by simp) hk)
      have hj : len a - (k + 1) < len a := by simp [tsub_lt_iff_left hk]
      obtain ⟨y, hy, _⟩ := A.cons_total_model p (nth a (len a - (k + 1))) (nth b 0)
        hp (ha _ hj) (Record.output_fiber A hb)
      refine ⟨adjoin y b, ?_⟩
      apply A.record_prepend ?_ hy
      have he : len a - (k + 1) + 1 = len a - k := by
        simpa using sub_succ_add_succ hk' (0 : M)
      simpa only [he] using hb
  simpa using hs (len a) (by rfl)

/-- Functionality is proved by backwards induction through the finite
record, using the T-provable functionality of nil and cons. -/
theorem record_unique {p a s k b d : M} (hb : A.Record p a s k b)
    (hd : A.Record p a s k d) : nth b 0 = nth d 0 := by
  have hi : ∀ i ≤ k, nth b (k - i) = nth d (k - i) := by
    intro i hik
    induction i using ISigma1.pi1_succ_induction
    · definability
    case zero =>
      simpa using (A.nilOp.total_model M p
        (A.nilOp.support_model M p (nth b k) hb.2.2.1).1).unique hb.2.2.1 hd.2.2.1
    case succ i ih =>
      have hi' : i < k := Arithmetic.succ_le_iff_lt.mp hik
      have hj : k - (i + 1) < k := by simp [tsub_lt_iff_left hik]
      have hprev := ih (le_trans (by simp) hik)
      have he : k - (i + 1) + 1 = k - i := by
        simpa using sub_succ_add_succ hi' (0 : M)
      have hstepb := hb.2.2.2 (k - (i + 1)) hj
      have hstepd := hd.2.2.2 (k - (i + 1)) hj
      rw [he] at hstepb hstepd
      rw [hprev] at hstepb
      exact A.cons_functional_model _ _ _ _ _ hstepb hstepd
  simpa using hi k (by rfl)

end ArithmeticModel

def evaluationFormula : 𝚺₁.Semisentence 3 :=
  let L := listCarrier V
  let R := A.recordFormula
  .mkSigma “p a y. !P.val p ∧ !L.val a ∧
    ∃ k b, !lenDef.val k a ∧ !R.val p a 0 k b ∧ !nthDef.val y b 0”

section Model

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T]

/-- Evaluation is total and has one output over the same parameter,
for every element of the full model satisfying the source predicates. -/
theorem evaluation_existsUnique [𝗣𝗔 ⪯ T] (p a : M)
    (hp : P.val.Evalb ![p]) (ha : (listCarrier V).val.Evalb ![a]) :
    ∃! y : M, A.evaluationFormula.val.Evalb ![p, a, y] := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  have hva : ∀ i < len a, V.val.Evalb ![nth a i] := by
    exact (FiniteSigmaOne.allEntriesCondition_eval V a).mp
      ((FiniteSigmaOne.finite_membership_model V a).mpr ha)
  obtain ⟨b, hb⟩ := A.record_exists p a hp hva
  have eval_iff (y : M) : A.evaluationFormula.val.Evalb ![p, a, y] ↔
      ∃ d : M, A.Record p a 0 (len a) d ∧ y = nth d 0 := by
    simp [evaluationFormula, hp, ha]
  refine ⟨nth b 0, (eval_iff _).mpr ⟨b, hb, rfl⟩, ?_⟩
  intro y hy
  obtain ⟨d, hd, rfl⟩ := (eval_iff y).mp hy
  exact A.record_unique hd hb

theorem evaluation_source [𝗣𝗔 ⪯ T] (p a y : M)
    (hy : A.evaluationFormula.val.Evalb ![p, a, y]) :
    P.val.Evalb ![p] ∧ (listCarrier V).val.Evalb ![a] := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  have h : P.val.Evalb ![p] ∧ (listCarrier V).val.Evalb ![a] ∧
      ∃ b : M, A.Record p a 0 (len a) b ∧ y = nth b 0 := by
    simpa [evaluationFormula] using hy
  exact ⟨h.1, h.2.1⟩

theorem evaluation_fiber [𝗣𝗔 ⪯ T] (p a y : M)
    (hy : A.evaluationFormula.val.Evalb ![p, a, y]) : A.Fiber p y := by
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  have h : P.val.Evalb ![p] ∧ (listCarrier V).val.Evalb ![a] ∧
      ∃ b : M, A.Record p a 0 (len a) b ∧ y = nth b 0 := by
    simpa [evaluationFormula] using hy
  obtain ⟨_, _, b, hb, rfl⟩ := h
  exact Record.output_fiber A hb

end Model

/-- The numerical graph reads the canonical pair of parameter and list. -/
def evaluationGraph : Graph :=
  let E := A.evaluationFormula
  .mkSigma “q y. ∃ p a, !pairDef.val q p a ∧ !E.val p a y”

variable [𝗣𝗔 ⪯ T]

def evaluationMorphism : GraphMorphism T (productCarrier P (listCarrier V)) X where
  graph := A.evaluationGraph
  support := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff, supportSentence_eval]
    intro q y hq
    have h : ∃ p a : M, q = Arithmetic.pair p a ∧
        A.evaluationFormula.val.Evalb ![p, a, y] := by
      simpa [evaluationGraph] using hq
    obtain ⟨p, a, he, hy⟩ := h
    have hs := A.evaluation_source p a y hy
    exact ⟨(productCarrier_eval P (listCarrier V) q).mpr ⟨p, a, he, hs.1, hs.2⟩,
      (A.evaluation_fiber p a y hy).1⟩
  total := by
    apply complete.{0} T
    intro M _ _
    let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
    rw [models_iff, totalSentence_eval]
    intro q hq
    obtain ⟨p, a, he, hp, ha⟩ := (productCarrier_eval P (listCarrier V) q).mp hq
    obtain ⟨y, hy, hu⟩ := A.evaluation_existsUnique p a hp ha
    refine ⟨y, ?_, ?_⟩
    · simpa [evaluationGraph] using Exists.intro p (Exists.intro a ⟨he, hy⟩)
    · intro z hz
      have h : ∃ p' a' : M, q = Arithmetic.pair p' a' ∧
          A.evaluationFormula.val.Evalb ![p', a', z] := by
        simpa [evaluationGraph] using hz
      obtain ⟨p', a', he', hz'⟩ := h
      obtain ⟨hp', ha'⟩ := (pair_eq_pair_iff _ _ _ _).mp (he'.symm.trans he)
      subst p'
      subst a'
      exact hu z hz'

def evaluationOverSentence : ArithmeticSentence :=
  let E := A.evaluationFormula
  let q := A.projection.graph
  “∀ p a y, !E.val p a y → !q.val y p”

/-- The resulting evaluation is provably over the same arbitrary parameter. -/
theorem evaluation_over : T ⊢ A.evaluationOverSentence := by
  apply complete.{0} T
  intro M _ _
  have h : ∀ p a y : M, A.evaluationFormula.val.Evalb ![p, a, y] →
      A.projection.graph.val.Evalb ![y, p] :=
    fun p a y hy => (A.evaluation_fiber p a y hy).2
  simpa [models_iff, evaluationOverSentence] using h

end SliceAlgebra

end CategoricalEssentialIncompleteness.V46.SyntacticListEvaluation
