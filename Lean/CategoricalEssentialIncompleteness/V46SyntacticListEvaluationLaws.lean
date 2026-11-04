/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
import CategoricalEssentialIncompleteness.V46SyntacticListEvaluation

/-! # The nil and cons equations of graph-defined parameter evaluation -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FailureOfComposition.ProofSearch FailureOfComposition.CodedObjectMembership
open CategoricalEssentialIncompleteness.V46.SyntacticPredicates

namespace CategoricalEssentialIncompleteness.V46.SyntacticListEvaluation

namespace SliceAlgebra

variable {T : ArithmeticTheory} {P V X : Carrier} (A : SliceAlgebra T P V X)

section Models

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [M↓[ℒₒᵣ] ⊧* T]

@[simp] theorem listCarrier_nil (V : Carrier) : (listCarrier V).val.Evalb (M := M) ![0] := by
  rw [listCarrier, ← FiniteSigmaOne.finite_membership_model,
    FiniteSigmaOne.allEntriesCondition_eval]
  simp

@[simp] theorem listCarrier_adjoin (V : Carrier) (v a : M) :
    (listCarrier V).val.Evalb ![adjoin v a] ↔
      V.val.Evalb ![v] ∧ (listCarrier V).val.Evalb ![a] := by
  simp only [listCarrier, ← FiniteSigmaOne.finite_membership_model,
    FiniteSigmaOne.allEntriesCondition_eval]
  constructor
  · intro h
    refine ⟨by simpa using h 0 (by simp), ?_⟩
    intro i hi
    simpa using h (i + 1) (by simpa using hi)
  · rintro ⟨hv, ha⟩ i hi
    rcases zero_or_succ i with rfl | ⟨j, rfl⟩
    · simpa using hv
    · have hj : j < len a := by simpa using hi
      simpa using ha j hj

omit [M↓[ℒₒᵣ] ⊧* T] in
@[simp] theorem evaluation_iff_record (p a y : M) :
    A.evaluationFormula.val.Evalb ![p, a, y] ↔
      P.val.Evalb ![p] ∧ (listCarrier V).val.Evalb ![a] ∧
        ∃ b : M, A.Record p a 0 (len a) b ∧ y = nth b 0 := by
  simp [evaluationFormula]

theorem evaluation_nil (p y : M) :
    A.evaluationFormula.val.Evalb ![p, 0, y] ↔ A.nilOp.graph.val.Evalb ![p, y] := by
  rw [evaluation_iff_record]
  constructor
  · rintro ⟨_, _, b, hb, hy⟩
    simpa only [len_nil, ← hy] using hb.2.2.1
  · intro hn
    refine ⟨(A.nilOp.support_model M p y hn).1, listCarrier_nil V,
      adjoin y 0, ?_, by simp⟩
    simpa using A.record_nil p 0 0 y hn

/-- Appending one new head value to a complete tail record gives the cons
recursion equation without assuming any external evaluator. -/
theorem evaluation_adjoin_intro (p v a x y : M)
    (hx : A.evaluationFormula.val.Evalb ![p, a, x])
    (hy : A.consOp.val.Evalb ![p, v, x, y]) :
    A.evaluationFormula.val.Evalb ![p, adjoin v a, y] := by
  obtain ⟨hp, ha, b, hb, he⟩ := (A.evaluation_iff_record p a x).mp hx
  have hv := (A.cons_support_model p v x y hy).2.1
  have htail : A.Record p (adjoin v a) 1 (len a) b := by
    refine ⟨hb.1, hb.2.1, hb.2.2.1, ?_⟩
    intro i hi
    simpa [add_comm 1 i] using hb.2.2.2 i hi
  have hy' : A.consOp.val.Evalb ![p, nth (adjoin v a) 0, nth b 0, y] := by
    simpa only [nth_adjoin_zero, he] using hy
  have hnew : A.Record p (adjoin v a) 0 (len a + 1) (adjoin y b) :=
    A.record_prepend (s := 0) (by simpa using htail) hy'
  apply (A.evaluation_iff_record p (adjoin v a) y).mpr
  refine ⟨hp, (listCarrier_adjoin V v a).mpr ⟨hv, ha⟩, adjoin y b, ?_, by simp⟩
  simpa using hnew

theorem evaluation_adjoin [𝗣𝗔 ⪯ T] (p v a y : M) :
    A.evaluationFormula.val.Evalb ![p, adjoin v a, y] ↔
      V.val.Evalb ![v] ∧ ∃ x : M, A.evaluationFormula.val.Evalb ![p, a, x] ∧
        A.consOp.val.Evalb ![p, v, x, y] := by
  constructor
  · intro h
    obtain ⟨hp, hva⟩ := A.evaluation_source p (adjoin v a) y h
    obtain ⟨hv, ha⟩ := (listCarrier_adjoin V v a).mp hva
    obtain ⟨x, hx, _⟩ := A.evaluation_existsUnique p a hp ha
    obtain ⟨z, hz, _⟩ := A.cons_total_model p v x hp hv (A.evaluation_fiber p a x hx)
    have he : y = z := (A.evaluation_existsUnique p (adjoin v a) hp hva).unique h
      (A.evaluation_adjoin_intro p v a x z hx hz)
    exact ⟨hv, x, hx, by simpa only [he] using hz⟩
  · rintro ⟨_, x, hx, hy⟩
    exact A.evaluation_adjoin_intro p v a x y hx hy

end Models

def nilEquationSentence : ArithmeticSentence :=
  let E := A.evaluationFormula
  let n := A.nilOp.graph
  “∀ p y, !E.val p 0 y ↔ !n.val p y”

def consEquationSentence : ArithmeticSentence :=
  let E := A.evaluationFormula
  let c := A.consOp
  “∀ p v a b y, !adjoinDef.val b v a →
    (!E.val p b y ↔ !V.val v ∧ ∃ x, !E.val p a x ∧ !c.val p v x y)”

variable [𝗣𝗔 ⪯ T]

theorem evaluation_nil_equation : T ⊢ A.nilEquationSentence := by
  apply complete.{0} T
  intro M _ _
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  have h : ∀ p y : M, A.evaluationFormula.val.Evalb ![p, 0, y] ↔
      A.nilOp.graph.val.Evalb ![p, y] := A.evaluation_nil
  simpa [models_iff, nilEquationSentence] using h

theorem evaluation_cons_equation : T ⊢ A.consEquationSentence := by
  apply complete.{0} T
  intro M _ _
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  have h : ∀ p v a b y : M, b = adjoin v a →
      (A.evaluationFormula.val.Evalb ![p, b, y] ↔ V.val.Evalb ![v] ∧
        ∃ x : M, A.evaluationFormula.val.Evalb ![p, a, x] ∧
          A.consOp.val.Evalb ![p, v, x, y]) := by
    rintro p v a b y rfl
    exact A.evaluation_adjoin p v a y
  simpa [models_iff, consEquationSentence] using h

/-- Unpack a represented numerical graph on the parameter/list product. -/
def unpackedGraph (H : Graph) : 𝚺₁.Semisentence 3 :=
  .mkSigma “p a y. ∃ q, !pairDef.val q p a ∧ !H.val q y”

section UniquenessModels

variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔] [M↓[ℒₒᵣ] ⊧* T]

@[simp] theorem unpackedGraph_eval (H : Graph) (p a y : M) :
    (unpackedGraph H).val.Evalb ![p, a, y] ↔ H.val.Evalb ![Arithmetic.pair p a, y] := by
  simp [unpackedGraph]

omit [𝗣𝗔 ⪯ T] in
theorem candidate_source (H : GraphMorphism T (productCarrier P (listCarrier V)) X)
    (p a y : M) (h : (unpackedGraph H.graph).val.Evalb ![p, a, y]) :
    P.val.Evalb ![p] ∧ (listCarrier V).val.Evalb ![a] := by
  have hs := (H.support_model M (Arithmetic.pair p a) y
    ((unpackedGraph_eval H.graph p a y).mp h)).1
  obtain ⟨p', a', he, hp, ha⟩ := (productCarrier_eval P (listCarrier V) _).mp hs
  obtain ⟨hp', ha'⟩ := (pair_eq_pair_iff _ _ _ _).mp he
  simpa only [hp', ha'] using And.intro hp ha

/-- The uniqueness induction has Pi-one complexity: both candidate graph
and value-record evaluation occur only as antecedents. -/
theorem evaluation_unique_model
    (H : GraphMorphism T (productCarrier P (listCarrier V)) X)
    (hn : ∀ p y : M, (unpackedGraph H.graph).val.Evalb ![p, 0, y] ↔
      A.nilOp.graph.val.Evalb ![p, y])
    (hc : ∀ p v a y : M, (unpackedGraph H.graph).val.Evalb ![p, adjoin v a, y] ↔
      V.val.Evalb ![v] ∧ ∃ x : M, (unpackedGraph H.graph).val.Evalb ![p, a, x] ∧
        A.consOp.val.Evalb ![p, v, x, y]) (p a y : M) :
    (unpackedGraph H.graph).val.Evalb ![p, a, y] ↔
      A.evaluationFormula.val.Evalb ![p, a, y] := by
  have hdef : 𝚷₁-Predicate (fun a : M => ∀ p x y : M,
      (unpackedGraph H.graph).val.Evalb ![p, a, x] →
        A.evaluationFormula.val.Evalb ![p, a, y] → x = y) := by
    let G : 𝚺₁.Semiformula M 3 := (unpackedGraph H.graph).rew Rew.emb
    let E : 𝚺₁.Semiformula M 3 := A.evaluationFormula.rew Rew.emb
    refine ⟨.mkPi “a. ∀ p x y, !G.val p a x → !E.val p a y → x = y”, ?_⟩
    intro v
    simp [G, E]
  have hfun : ∀ a p x y : M, (unpackedGraph H.graph).val.Evalb ![p, a, x] →
      A.evaluationFormula.val.Evalb ![p, a, y] → x = y := by
    intro a
    induction a using adjoin_ISigma1.pi1_succ_induction
    · exact hdef
    case nil =>
      intro p x y hx hy
      have hx' := (hn p x).mp hx
      have hy' := (A.evaluation_nil p y).mp hy
      exact (A.nilOp.total_model M p (A.nilOp.support_model M p x hx').1).unique hx' hy'
    case adjoin v a ih =>
      intro p x y hx hy
      obtain ⟨_, u, hu, hcu⟩ := (hc p v a x).mp hx
      obtain ⟨_, z, hz, hcz⟩ := (A.evaluation_adjoin p v a y).mp hy
      have he := ih p u z hu hz
      subst u
      exact A.cons_functional_model p v z x y hcu hcz
  constructor
  · intro h
    obtain ⟨hp, ha⟩ := candidate_source H p a y h
    obtain ⟨z, hz, _⟩ := A.evaluation_existsUnique p a hp ha
    have he := hfun a p y z h hz
    simpa only [he] using hz
  · intro h
    obtain ⟨hp, ha⟩ := A.evaluation_source p a y h
    have hs := (productCarrier_eval P (listCarrier V) (Arithmetic.pair p a)).mpr
      ⟨p, a, rfl, hp, ha⟩
    obtain ⟨z, hz, _⟩ := H.total_model M (Arithmetic.pair p a) hs
    have hz' := (unpackedGraph_eval H.graph p a z).mpr hz
    have he := hfun a p z y hz' h
    simpa only [he] using hz'

end UniquenessModels

/-- Equality as actual predicate-category arrows follows from the internal
uniqueness induction, for arbitrary candidate morphisms satisfying the laws. -/
theorem evaluation_unique
    (H : GraphMorphism T (productCarrier P (listCarrier V)) X)
    (hn : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] (p y : M),
      (unpackedGraph H.graph).val.Evalb ![p, 0, y] ↔ A.nilOp.graph.val.Evalb ![p, y])
    (hc : ∀ (M : Type) [ORingStructure M] [M↓[ℒₒᵣ] ⊧* T] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔]
      (p v a y : M),
      (unpackedGraph H.graph).val.Evalb ![p, adjoin v a, y] ↔
        V.val.Evalb ![v] ∧ ∃ x : M, (unpackedGraph H.graph).val.Evalb ![p, a, x] ∧
          A.consOp.val.Evalb ![p, v, x, y]) :
    representedArrow T H = representedArrow T A.evaluationMorphism := by
  apply Quotient.sound
  apply complete.{0} T
  intro M _ _
  let : M↓[ℒₒᵣ] ⊧* 𝗣𝗔 := models_of_subtheory (U := T) inferInstance
  rw [models_iff, uniformSentence_eval]
  intro q y
  let p := π₁ q
  let a := π₂ q
  have he : q = Arithmetic.pair p a := by simp [p, a]
  rw [he]
  change H.graph.val.Evalb ![Arithmetic.pair p a, y] ↔
    A.evaluationGraph.val.Evalb ![Arithmetic.pair p a, y]
  have h := A.evaluation_unique_model H (hn M) (hc M) p a y
  simpa [unpackedGraph, evaluationGraph] using h

end SliceAlgebra

end CategoricalEssentialIncompleteness.V46.SyntacticListEvaluation
